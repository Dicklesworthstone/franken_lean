//! Intro and funext use the same checked term-pattern introduction machinery.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};
fn engine() -> Engine {
    let base = Engine::with_source_seed(EngineAdmissionLimits::new(Budget::for_stack_bytes(
        2 * 1024 * 1024,
    )))
    .unwrap()
    .into_complete()
    .unwrap();
    check(
        &base,
        "structure Prod (A B : Type) where\n  fst : A\n  snd : B",
    )
}
fn check(base: &Engine, source: &str) -> Engine {
    base.check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(
            2 * 1024 * 1024,
        ))),
    )
    .unwrap_or_else(|e| panic!("{source}\n{e:?}"))
    .into_complete()
    .unwrap()
    .engine
}
#[test]
fn typed_introductions_use_the_original_context_and_refine_the_visible_domain() {
    let base = engine();
    for source in [
        "def Alias : Type := Nat\ntheorem t : (x : Alias) -> x = x := by intro (x : Nat); rfl",
        "theorem t (A : Type) : A -> True := by intro (A : A); constructor",
        "theorem t (A : Type) : A -> True := by intro (_ : A); constructor",
        "theorem t : let x := 3; x = x := by intro (x : Nat); rfl",
        "theorem t : Nat -> True := by intro (x : _); constructor",
        "theorem t : Nat -> True := by intro (x :); constructor",
        "def Alias : Type := Nat\ntheorem t (f g : Alias -> Nat) (h : (x : Nat) -> f x = g x) : f = g := by funext (x : Nat); exact h x",
        "theorem t (F : Nat -> Type) (f g : (n : Nat) -> F n -> Nat) (h : (n : Nat) -> (a : F n) -> f n a = g n a) : f = g := by funext (n : Nat) (a : F n); exact h n a",
    ] {
        check(&base, source);
    }
}
#[test]
fn tuple_and_constructor_introductions_reuse_checked_pattern_elimination() {
    let base = engine();
    for source in [
        "theorem t (P Q : Prop) : P ∧ Q -> Q ∧ P := by intro ⟨hp, hq⟩; exact And.intro hq hp",
        "theorem t : (p : Nat × Nat) -> p.1 = p.1 := by intro (a, b); rfl",
        "theorem t (f g : Nat × Nat -> Nat) (h : (a b : Nat) -> f (a, b) = g (a, b)) : f = g := by funext (a, b); exact h a b",
        "theorem t (f g : Nat × Nat -> Nat × Nat -> Nat) (h : (a b c d : Nat) -> f (a, b) (c, d) = g (a, b) (c, d)) : f = g := by funext (a, b) (c, d); exact h a b c d",
        "theorem t (f g : Nat × (Nat × Nat) -> Nat) (h : (a b c : Nat) -> f (a, (b, c)) = g (a, (b, c))) : f = g := by funext (a, (b, c)); exact h a b c",
    ] {
        check(&base, source);
    }
}
#[test]
fn patterns_keep_later_dependent_binders_and_focus_boundaries() {
    let base = engine();
    for source in [
        "theorem t (P Q : Prop) : (P ∧ Q -> P) ∧ True := by\n  constructor\n  · intro ⟨hp, hq⟩\n    exact hp\n  · constructor",
        "theorem t (f g : Nat × Nat -> Nat) (h : (a b : Nat) -> f (a, b) = g (a, b)) : f = g := by\n  first | (funext (a, b); fail) | skip\n  guard_target = f = g\n  funext (x, y)\n  exact h x y",
        "theorem t (P Q : Prop) : P ∧ Q -> True -> P := by intro ⟨hp, hq⟩ h; exact hp",
    ] {
        check(&base, source);
    }
}
#[test]
fn pattern_errors_cannot_invent_fields_evidence_or_annotation_scope() {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    for source in [
        "theorem bad : Nat -> True := by intro (n : Bool); constructor",
        "theorem bad : (A : Type) -> True := by intro (A : A); constructor",
        "theorem bad (P Q : Prop) : P ∧ Q -> True := by intro (a, b); constructor",
        "theorem bad (P Q : Prop) : P ∨ Q -> True := by intro ⟨a, b⟩; constructor",
        "theorem bad : Nat × Nat -> True := by intro (x, x); constructor",
        "theorem bad (f g : Nat × Nat -> Nat) : f = g := by funext (a, b); rfl",
        "theorem bad (f : Nat -> Nat) : f = f := by funext (x : Bool); rfl",
        "theorem bad (x y : Nat) : Nat -> Nat -> True := by intro (x y); constructor",
    ] {
        assert!(
            base.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(
                    2 * 1024 * 1024
                )))
            )
            .is_err(),
            "{source}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
    }
    check(
        &base,
        "theorem t (P Q : Prop) : P ∧ Q -> P := by intro ⟨h, _⟩; exact h",
    );
}
