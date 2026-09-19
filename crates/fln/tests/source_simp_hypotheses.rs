//! Wildcard selection uses actual local proof identities and checked transports.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Outcome, SourceCheckLimits};

fn limits() -> SourceCheckLimits {
    SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(
        2 * 1024 * 1024,
    )))
}
fn engine() -> Engine {
    Engine::with_source_seed(EngineAdmissionLimits::new(Budget::for_stack_bytes(
        2 * 1024 * 1024,
    )))
    .unwrap()
    .into_complete()
    .unwrap()
}
fn check(base: &Engine, source: &str) {
    base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .expect("must complete");
}
fn refuse(base: &Engine, source: &str) {
    let root = base.logical_root(&KVMap::new());
    let result = base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits());
    assert!(!matches!(result, Ok(Outcome::Complete(_))), "{source}");
    assert_eq!(root, base.logical_root(&KVMap::new()));
}

#[test]
fn wildcard_uses_equalities_equivalences_and_condition_evidence() {
    let base = engine();
    check(
        &base,
        r#"
      theorem equality (f : Nat -> Nat) (x : Nat) (h : f x = x) : f (f x) = x := by simp only [*]
      theorem equivalence (P Q : Prop) (h : P ↔ Q) (q : Q) : P := by simp only [*]
      theorem condition (f : Nat -> Nat) (P : Nat -> Prop) (x : Nat)
          (h : ∀ n : Nat, P n -> f n = n) (p : P x) : f x = x := by simp only [*]
      theorem nested (P : Prop) : P -> P := by intro h; simp only [*]
      theorem localHave (P : Prop) (p : P) : P := by have h : P := p; simp only [*]
    "#,
    );
}

#[test]
fn wildcard_keeps_shadowed_proof_identities_and_ignores_nonproof_data() {
    let base = engine();
    check(
        &base,
        r#"
      theorem shadow (P Q : Prop) (h : P) : Q -> P := by intro h; simp only [*]
      theorem data (P : Prop) (x : Nat) (h : P) : P := by simp only [*, *]
    "#,
    );
    for source in [
        "theorem falseProof (P : Prop) (n : Nat) : P := by simp only [*]",
        "theorem condition (f : Nat -> Nat) (P : Prop) (x : Nat) (h : P -> f x = x) : f x = x := by simp only [*]",
        "theorem data (A : Type) (x : A) : A := by simp only [*]",
    ] {
        refuse(&base, source);
    }
}

#[test]
fn wildcard_locations_remap_replaced_locals_and_exclude_self_evidence() {
    let base = engine();
    check(
        &base,
        r#"
      theorem transport (P : Nat -> Prop) (x y : Nat) (h : x = y) (hx : P x) : P y := by
        simp only [*] at hx
        exact hx
      theorem together (P : Nat -> Prop) (x y : Nat) (h : x = y) (hx : P x) : P y := by
        simp only [*] at hx ⊢
    "#,
    );
    refuse(
        &base,
        "theorem self (x y : Nat) (h : x = y) : x = y := by simp only [*] at h; exact h",
    );
}

#[test]
fn failed_wildcard_alternatives_restore_the_proof_context() {
    let base = engine();
    check(
        &base,
        r#"
      theorem rollback (P Q : Prop) (p : P) : P := by
        first | (simp only [*]; fail) | exact p
      theorem branch (P Q : Prop) (p : P) (q : Q) : P ∧ Q := by
        constructor
        · simp only [*]
        · simp only [*]
    "#,
    );
}
