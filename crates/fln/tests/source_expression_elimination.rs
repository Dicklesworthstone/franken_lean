//! Expression discriminants use generalized, council-checked recursor proofs.
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

fn check(source: &str) {
    engine()
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap();
}

#[test]
fn computed_cases_rewrite_the_goal_without_fabricating_evidence() {
    check(
        "def mirror (b : Bool) : Bool := match b with | .false => false | .true => true
      theorem allValues (f : Nat -> Bool) (n : Nat) : mirror (f n) = f n := by
        cases f n with | false => rfl | true => rfl",
    );
    check("theorem concrete : (0 : Nat) = 0 := by cases 0 with | zero => rfl | succ n => rfl");
    check(
        "theorem openGoals (f : Nat -> Bool) (n : Nat) : f n = f n := by
      cases f n
      rfl
      rfl",
    );
    check(
        "theorem groupedLocal (n : Nat) (h : n = n) : n = n := by
      cases (n) with | zero => exact h | succ k => exact h",
    );
}

#[test]
fn equation_witnesses_connect_original_hypotheses_to_each_constructor() {
    for tactic in ["cases", "induction"] {
        check(&format!(
            "theorem keep (f : Nat -> Bool) (n : Nat) (P : Bool -> Prop)
            (p : P (f n)) : P (f n) := by
          {tactic} h : f n with
          | false => rw [<- h]; exact p
          | true => rw [<- h]; exact p"
        ));
    }
    check(
        "theorem originalLocal (n : Nat) (P : Nat -> Prop) (p : P n) : P n := by
      cases h : n with | zero => rewrite [<- h]; exact p | succ k => rewrite [<- h]; exact p",
    );
    check(
        "theorem anonymousEquation (f : Nat -> Bool) (n : Nat) : f n = f n := by
      cases _ : f n with | false => rfl | true => rfl",
    );
}

#[test]
fn expression_induction_exposes_real_hypotheses_and_generalized_parameters() {
    check(
        "def copy (n : Nat) : Nat := match n with | .zero => 0 | .succ k => Nat.succ (copy k)
      theorem copied (f : Nat -> Nat) (n : Nat) : copy (f n) = f n := by
        induction (f n) with | zero => rfl | succ k ih => simp only [copy, ih]",
    );
    check("def zeroAcc (n acc : Nat) : Nat := match n with | .zero => 0 | .succ k => zeroAcc k (acc + 1)
      theorem allAcc (f : Nat -> Nat) (n acc : Nat) : zeroAcc (f n) acc = 0 := by
        induction (f n) generalizing acc with | zero => rfl | succ k ih => exact ih (acc + 1)");
}

#[test]
fn dependent_results_universes_and_fixed_indices_keep_their_types() {
    check(
        "structure Package where
        carrier : Type
        value : carrier
      def unpack (f : Nat -> Package) (n : Nat) : (f n).carrier := by
        cases f n with | mk A a => exact a",
    );
    check(
        "universe u
      inductive Box (A : Type u) where | mk (value : A)
      def unbox {A : Type u} (f : Nat -> Box A) (n : Nat) : A := by
        cases f n with | mk value => exact value",
    );
    check(
        "inductive At : Bool -> Type where | no : At false | yes : At true
      theorem possible (f : Nat -> At true) (n : Nat) : true = true := by
        cases h : f n with | yes => rfl",
    );
}

#[test]
fn nested_splits_and_failed_alternatives_restore_their_contexts() {
    check(
        "theorem nested (f g : Nat -> Bool) (n : Nat) : f n = f n := by
      cases h : f n with
      | false =>
        cases h : g n with | false => rfl | true => rfl
      | true => rfl",
    );
    check(
        "theorem fallback (f : Nat -> Bool) (n : Nat) : f n = f n := by
      first
      | cases h : f n with | false => fail | true => rfl
      | rfl",
    );
    check(
        "theorem afterIntro : forall (n : Nat), n = n := by
      intro n
      have p : n = n := by rfl
      cases h : n with | zero => rewrite [<- h]; exact p | succ k => rewrite [<- h]; exact p",
    );
}

#[test]
fn invalid_or_incomplete_expression_eliminations_never_publish() {
    let base = engine();
    for source in [
        "theorem bad : (0 : Nat) = 1 := by cases 0 with | zero => rfl | succ n => rfl",
        "theorem bad (f : Nat -> Bool) (n : Nat) : f n = f n := by cases f n with | false => rfl",
        "theorem bad (f : Nat -> Bool) (n : Nat) : f n = f n := by cases f n with | false => rfl | true => exact h",
        "theorem bad (n : Nat) : n = n := by cases (n : Bool) with | false => rfl | true => rfl",
        "theorem bad (n : Nat) : n = n := by cases (fun (x : Nat) => x) with | zero => rfl | succ k => rfl",
        "theorem bad (n : Nat) : n = n := by cases _",
        "theorem bad (f : Nat -> Bool) (n : Nat) (P : Bool -> Prop) (p : P (f n)) : P (f n) := by cases f n with | false => exact p | true => exact p",
        "theorem bad : (0 : Nat) = 0 := by cases ((fun (n : Nat) => true) false) with | false => rfl | true => rfl",
        "theorem bad (b : Bool) : b = b := by cases (let x : Nat := false; b) with | false => rfl | true => rfl",
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
    }
    check("theorem recovered : (3 : Nat) = 3 := by rfl");
}

#[test]
fn empty_and_propositional_discriminants_keep_the_kernel_elimination_boundary() {
    check(
        "inductive Void where
      def absurdExpression (f : Nat -> Void) (n : Nat) : Nat := by cases f n",
    );
    check(
        "theorem switch (P Q : Prop) (f : Nat -> (P ∨ Q)) (n : Nat) : Q ∨ P := by
      cases f n with | inl p => right; exact p | inr q => left; exact q",
    );
    assert!(engine().check_source_files(
        &[b"def forbidden (P Q : Prop) (f : Nat -> Or P Q) (n : Nat) : Nat := by cases f n with | inl p => exact 0 | inr q => exact 1"],
        &KVMap::new(), SourceCheckLimits::new(limits())
    ).is_err());
}

#[test]
fn exhausted_expression_elimination_is_a_nonanswer_not_a_fallback_success() {
    let base = engine();
    let mut low = SourceCheckLimits::new(limits());
    low.admission.kernel = low.admission.kernel.narrowed(0, 32);
    let result = base.check_source_files(
        &[b"theorem self (f : Nat -> Bool) (n : Nat) : f n = f n := by\n  first\n  | cases h : f n with | false => rfl | true => rfl\n  | rfl"],
        &KVMap::new(), low,
    );
    match result {
        Ok(fln::Outcome::Inconclusive(_)) => {}
        Err(error) => assert!(
            matches!(error.disposition(), ("resource" | "inconclusive", false, 3)),
            "{error:?}"
        ),
        other => panic!("expected a typed nonanswer: {other:?}"),
    }
}
