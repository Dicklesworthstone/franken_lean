//! Simplifying under quantified propositions preserves their external binders.
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
fn check(base: &Engine, source: &str) {
    base.check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits()),
    )
    .unwrap_or_else(|e| panic!("{source}\n{e:?}"))
    .into_complete()
    .unwrap();
}

#[test]
fn quantified_rewrite_preserves_the_binder_and_does_not_introduce_a_local() {
    let base = engine();
    for source in [
        "theorem t (f g : Nat -> Nat) (R : Nat -> Prop) (h : (n : Nat) -> f n = g n) (ready : (n : Nat) -> R (g n)) : (n : Nat) -> R (f n) := by\n  simp only [h]\n  guard_target = (n : Nat) -> R (g n)\n  exact ready",
        "theorem t (f g : Nat -> Nat) (R : Nat -> Prop) (h : (n : Nat) -> f n = g n) (ready : (n : Nat) -> R (f n)) : (n : Nat) -> R (g n) := by\n  simp only [<- h]\n  exact ready",
        "theorem t (f g : Nat -> Nat) (R : Nat -> Prop) (h : (n : Nat) -> f n = g n) (ready : (n : Nat) -> R (g n)) : (h : Nat) -> R (f h) := by simp only [h]; exact ready",
    ] {
        check(&base, source);
    }
}

#[test]
fn quantified_reflexivity_and_truth_close_without_widening_conversion() {
    let base = engine();
    for source in [
        "theorem t (A : Type) : (x : A) -> x = x := by simp only []",
        "theorem t (A : Type) (B : A -> Type) : (a : A) -> (b : B a) -> b = b := by simp only []",
        "theorem t (A : Type) : (a : A) -> True := by simp only []",
        "theorem t (f g : Nat -> Nat) (h : (n : Nat) -> f n = g n) : (n : Nat) -> f n = g n := by simp only [h]",
    ] {
        check(&base, source);
    }
    let source = "def wrapped (n : Nat) : Nat := n\ntheorem bad : (n : Nat) -> wrapped n = n := by simp only []";
    assert!(
        base.check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits())
        )
        .is_err()
    );
}

#[test]
fn nested_dependent_quantifiers_hypotheses_and_simpa_share_binder_rewriting() {
    let base = engine();
    for source in [
        "universe u v\ntheorem t (A : Sort u) (B : A -> Sort v) (f g : (a : A) -> B a -> Nat) (R : Nat -> Prop) (h : (a : A) -> (b : B a) -> f a b = g a b) (ready : (a : A) -> (b : B a) -> R (g a b)) : (a : A) -> (b : B a) -> R (f a b) := by simp only [h]; exact ready",
        "theorem t (f g : Nat -> Nat) (R : Nat -> Prop) (h : (n : Nat) -> f n = g n) (ready : (n : Nat) -> R (f n)) : (n : Nat) -> R (g n) := by simp only [h] at ready; exact ready",
        "theorem t (f g : Nat -> Nat) (R : Nat -> Prop) (h : (n : Nat) -> f n = g n) (ready : (n : Nat) -> R (f n)) : (n : Nat) -> R (g n) := by simpa only [h] using ready",
        "theorem t (f g : Nat -> Nat) (R : Nat -> Prop) (h : (n : Nat) -> f n = g n) (ready : (n : Nat) -> R (f n)) : (n : Nat) -> R (g n) := by simp_all only [h]",
        "theorem t (F G : Nat -> Nat -> Nat) (wrap : (Nat -> Nat) -> Prop) (h : (n x : Nat) -> F n x = G n x) (ready : (n : Nat) -> wrap (fun x => G n x)) : (n : Nat) -> wrap (fun x => F n x) := by simp only [h]; exact ready",
    ] {
        check(&base, source);
    }
}

#[test]
fn registered_rules_and_equivalences_keep_their_proof_paths_beneath_binders() {
    let base = engine();
    for source in [
        "def wrapped (n : Nat) : Nat := n\n@[simp] theorem unwrap (n : Nat) : wrapped n = n := by rfl\ntheorem t : (n : Nat) -> wrapped n = n := by simp",
        "def wrapped (n : Nat) : Nat := n\n@[simp] theorem unwrap (n : Nat) : wrapped n = n := by rfl\ntheorem t (unwrap : False) : (fun n => wrapped n) = (fun n => n) := by simp",
        "theorem t (P Q : Nat -> Prop) (h : (n : Nat) -> (P n ↔ Q n)) (ready : (n : Nat) -> Q n) : (n : Nat) -> P n := by simp only [h]; exact ready",
        "theorem t (f g : Nat -> Nat) (h : (n : Nat) -> f n = g n) (ready : (fun n => f n) = g) : (fun n => g n) = g := by simp only [h] at ready; exact ready",
    ] {
        check(&base, source);
    }
}

#[test]
fn quantified_simp_cannot_capture_or_invent_premises() {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    for source in [
        "theorem bad (f g : Nat -> Nat) (h : f 0 = g 0) : (n : Nat) -> f n = g n := by simp only [h]",
        "theorem bad (f g : Nat -> Nat) (P : Nat -> Prop) (h : (n : Nat) -> P n -> f n = g n) (hp : (n : Nat) -> P n) : (n : Nat) -> f n = g n := by simp only [h]",
        "theorem bad (A : Type) : (n : Nat) -> A := by simp only []",
        // This increment rewrites quantified propositions, not arbitrary
        // dependent function types. Their type transport needs another motive.
        "theorem bad (A : Type) (B C : A -> Type) (h : (a : A) -> B a = C a) : ((a : A) -> B a) = ((a : A) -> C a) := by simp only [h]",
    ] {
        assert!(
            base.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits())
            )
            .is_err(),
            "{source}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
    }
    check(
        &base,
        "theorem t (f g : Nat -> Nat) (P : Nat -> Prop) (h : (n : Nat) -> P n -> f n = g n) (hp : (n : Nat) -> P n) : (n : Nat) -> f n = g n := by simp only [h, hp]",
    );
}
