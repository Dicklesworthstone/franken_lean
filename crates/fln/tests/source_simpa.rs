//! Independent simplification of evidence and goals, with real closure required.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Outcome, SourceCheckLimits};
fn engine() -> Engine {
    Engine::with_source_seed(EngineAdmissionLimits::new(Budget::for_stack_bytes(
        2 * 1024 * 1024,
    )))
    .unwrap()
    .into_complete()
    .unwrap()
}
fn check(base: &Engine, source: &str) {
    base.check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(
            2 * 1024 * 1024,
        ))),
    )
    .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
    .into_complete()
    .expect("must complete");
}
fn refuse(base: &Engine, source: &str) {
    let root = base.logical_root(&KVMap::new());
    let result = base.check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(
            2 * 1024 * 1024,
        ))),
    );
    assert!(!matches!(result, Ok(Outcome::Complete(_))), "{source}");
    assert_eq!(root, base.logical_root(&KVMap::new()));
}

#[test]
fn simpa_normalizes_both_sides_and_completes_with_explicit_or_local_evidence() {
    let base = engine();
    check(
        &base,
        r#"
      theorem supplied (P : Nat -> Prop) (f g : Nat -> Nat) (x : Nat)
          (hf : f x = x) (hg : g x = x) (p : P (f x)) : P (g x) := by
        simpa only [hf, hg] using p
      theorem local (P : Nat -> Prop) (f g : Nat -> Nat) (x : Nat)
          (hf : f x = x) (hg : g x = x) (p : P (f x)) : P (g x) := by
        simpa only [hf, hg]
      theorem wildcard (P : Nat -> Prop) (f g : Nat -> Nat) (x : Nat)
          (hf : f x = x) (hg : g x = x) (p : P (f x)) : P (g x) := by
        simpa only [*] using p
      theorem reflexive (x : Nat) : x = x := by simpa only []
      theorem application (x : Nat) : x = x := by simpa only [] using (Eq.refl x)
      theorem universeProof.{u} {A : Sort u} (x : A) : x = x := by
        simpa only [] using (Eq.refl x)
      theorem inferredUniverse {A : Sort _} (x : A) : x = x := by
        simpa only [] using (Eq.refl x)
      theorem lets (P : Nat -> Prop) (n : Nat) (p : P n) : P n := by
        let x := n
        have hx : P x := p
        simpa only [x] using hx
    "#,
    );
}

#[test]
fn simpa_handles_registered_equivalences_unfolding_and_type_valued_goals() {
    let base = engine();
    check(
        &base,
        r#"
      def wrap (P : Prop) : Prop := P
      @[simp] theorem unwrap (P : Prop) : wrap P ↔ P := by
        constructor
        · intro h; exact h
        · intro h; exact h
      theorem withDefaults (P : Prop) (h : wrap (wrap P)) : P := by simpa using h
      theorem selected (P : Prop) (h : wrap P) : P := by simpa only [wrap] using h
      def transport (F : Nat -> Type) (f g : Nat -> Nat) (x : Nat)
          (hf : f x = x) (hg : g x = x) (p : F (f x)) : F (g x) := by
        simpa only [hf, hg] using p
    "#,
    );
}

#[test]
fn simpa_requires_completion_and_keeps_using_evidence_out_of_the_rule_set() {
    let base = engine();
    for source in [
        "theorem missing (P Q : Prop) (p : P) : Q := by simpa using p",
        "theorem falseProof : (0 : Nat) = 1 := by simpa using (Eq.refl 0)",
        "theorem progress (P : Nat -> Prop) (x y : Nat) (h : x = y) : P x := by simpa only [h]; fail",
        "theorem unknown (P : Prop) (p : P) : P := by simpa only [missing] using p",
        "theorem self (P Q : Prop) (h : P ↔ Q) (p : P) : Q := by simpa only [] using p",
        "theorem badAnnotation (P Q : Prop) (p : P) (q : Q) : P := by simpa using (q : P)",
        "def discard (P Q : Prop) (p : P) (q : Q) : P := p\ntheorem erased (P Q : Prop) (p : P) : P := by simpa using (discard P Q p (p : Q))",
    ] {
        refuse(&base, source);
    }
}

#[test]
fn simpa_failed_alternatives_preserve_siblings_and_original_context() {
    let base = engine();
    check(
        &base,
        r#"
      theorem alternatives (P Q : Prop) (p : P) (q : Q) : P := by
        first | simpa only [] using q | simpa only [] using p
      theorem noProgressIsFailure (P : Nat -> Prop) (x y : Nat) (h : x = y) (p : P x) : P x := by
        first | simpa only [h] using h | exact p
      def discard (P Q : Prop) (p : P) (q : Q) : P := p
      theorem discardedArgumentIsStillChecked (P Q : Prop) (p : P) : P := by
        first | simpa using (discard P Q p (p : Q)) | exact p
      theorem wrongAnnotationIsRecoverable (P Q : Prop) (p : P) (q : Q) : P := by
        first | simpa using (q : P) | exact p
      theorem siblings (P Q : Prop) (p : P) (q : Q) : P ∧ Q := by
        constructor
        · simpa only [] using p
        · simpa only [] using q
    "#,
    );
}

#[test]
fn simpa_composes_with_true_false_and_keeps_supplied_proofs_out_of_the_simp_set() {
    let base = engine();
    check(
        &base,
        r#"
      theorem trueGoal : True := by simpa only []
      theorem trueUsing (P : Prop) (p : P) : True := by simpa only [p] using p
      theorem viaWildcard (P : Prop) (p : P) : P := by simpa only [*] using p
      def typeTransport (F : Prop -> Type) (P : Prop) (p : P) (value : F True) : F P := by
        simpa only [p] using value
      theorem mismatchFallback (P : Prop) (p : P) : P := by
        first | simpa only [] using True.intro | exact p
    "#,
    );
    // The generated private evidence local is not itself a simp hypothesis.
    refuse(
        &base,
        "theorem notARewrite (P : Prop) (p : P) : True := by simpa only [] using p",
    );
    refuse(
        &base,
        "theorem falseGoal (P : Prop) (np : ¬ P) : P := by simpa only [np]",
    );
}
