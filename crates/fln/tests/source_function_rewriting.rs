//! Function-valued occurrences must reach the real rewrite matcher and council.
#![forbid(unsafe_code)]

use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Name, SourceCheckLimits};
use fln_env::constants::ConstantInfo;

fn limits() -> SourceCheckLimits {
    SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(
        2 * 1024 * 1024,
    )))
}

fn engine() -> Engine {
    Engine::with_source_seed(limits().admission)
        .unwrap()
        .into_complete()
        .unwrap()
}

fn checked(base: &Engine, source: &str, theorem: &str) -> Engine {
    let result = base
        .check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .expect("both native checkers must complete")
        .engine;
    assert!(matches!(
        result.environment().find(&Name::from_components([theorem])),
        Some(ConstantInfo::Thm(_))
    ));
    result
}

#[test]
fn rewrite_matches_bare_function_constants_in_both_directions() {
    let base = engine();
    for tactic in ["rw [h]", "rw [← h]", "rewrite [h]; rfl"] {
        checked(
            &base,
            &format!(
                "def original (n : Nat) : Nat := n\n\
                 theorem changed (g : Nat → Nat) (h : original = g) (n : Nat) :\n\
                 original n = g n := by {tactic}"
            ),
            "changed",
        );
    }
}

#[test]
fn rewrite_matches_partially_applied_function_constants() {
    checked(
        &engine(),
        "def original (n m : Nat) : Nat := n\n\
         theorem changed (g : Nat → Nat) (k n : Nat) (h : original k = g) :\n\
         original k n = g n := by rw [h]",
        "changed",
    );
}

#[test]
fn simp_only_matches_function_equalities_without_default_unfolding() {
    checked(
        &engine(),
        "def original (n : Nat) : Nat := n\n\
         theorem changed (g : Nat → Nat) (h : original = g) (n : Nat) :\n\
         original n = g n := by simp only [h]",
        "changed",
    );
}

#[test]
fn function_rewriting_transports_a_hypothesis() {
    checked(
        &engine(),
        "def original (n : Nat) : Nat := n\n\
         theorem changed (P : (Nat → Nat) → Prop) (g : Nat → Nat)\n\
         (h : original = g) (hp : P original) : P g := by rw [h] at hp; exact hp",
        "changed",
    );
}

#[test]
fn unrelated_function_equality_is_refused_without_publishing_partial_state() {
    let base = engine();
    let source = "def original (n : Nat) : Nat := n\n\
        theorem invalid (P : (Nat → Nat) → Prop) (f g : Nat → Nat)\n\
        (h : f = g) (hp : P original) : P g := by rw [h] at hp; exact hp";
    let before = base.logical_root(&KVMap::new());
    let error = base
        .check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_err();
    assert!(error.to_string().contains("rewrite"), "{error:?}");
    assert_eq!(base.logical_root(&KVMap::new()), before);
    assert!(
        !base
            .environment()
            .contains(&Name::from_components(["invalid"]))
    );
    checked(
        &base,
        "theorem recovery (x : Nat) : x = x := by rfl",
        "recovery",
    );
}

#[test]
fn dependent_partial_function_types_remain_rewrite_candidates() {
    checked(
        &engine(),
        "def original (A : Type) (n : Nat) (x : A) : A := x\n\
         theorem changed (A : Type) (g : A → A) (k : Nat) (h : original A k = g) (x : A) :\n\
         original A k x = g x := by rw [h]",
        "changed",
    );
}
