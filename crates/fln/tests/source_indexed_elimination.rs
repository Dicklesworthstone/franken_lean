//! Indexed eliminations use admitted recursors and both production checkers.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Outcome, SourceCheckLimits};

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn engine() -> Engine {
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}
fn check(source: &str) -> fln::SourceFileCheck {
    engine()
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .unwrap_or_else(|e| panic!("{source}\n{e:?}"))
        .into_complete()
        .unwrap()
}
const VEC: &str = "inductive Vec (A : Type) : Nat -> Type where | nil : Vec A 0 | cons (n : Nat) (head : A) (tail : Vec A n) : Vec A (Nat.succ n)\n";
const LENGTH: &str = "def length {A : Type} (n : Nat) (xs : Vec A n) : Nat := by\n  induction xs with\n  | nil => exact 0\n  | cons k x tail ih => exact Nat.succ ih\n";
const COPY: &str = "def copy {A : Type} (n : Nat) (xs : Vec A n) : Vec A n := by\n  induction xs with\n  | nil => exact Vec.nil\n  | cons k x tail ih => exact Vec.cons k x ih\n";

#[test]
fn indexed_induction_computes_length_and_proves_it_equals_the_index() {
    check(&format!(
        "{VEC}{LENGTH}\
        theorem length_ok {{A : Type}} (n : Nat) (xs : Vec A n) : length n xs = n := by\n  induction xs with\n  | nil => rfl\n  | cons k x tail ih => simp only [length, ih]\n\
        theorem example : length 2 (Vec.cons 1 7 (Vec.cons 0 9 Vec.nil)) = 2 := by rfl"
    ));
}

#[test]
fn indexed_induction_can_return_data_at_the_refined_index() {
    check(&format!(
        "{VEC}{COPY}\
        theorem copy_ok {{A : Type}} (n : Nat) (xs : Vec A n) : copy n xs = xs := by\n  induction xs with\n  | nil => rfl\n  | cons k x tail ih => simp only [copy, ih]\n\
        theorem example : copy 1 (Vec.cons 0 7 Vec.nil) = Vec.cons 0 7 Vec.nil := by rfl"
    ));
}

#[test]
fn dependent_index_telescopes_are_abstracted_in_family_order() {
    check(
        "inductive Witness (A : Type) (P : A -> Type) : forall a : A, P a -> Type where | intro (a : A) (value : P a) : Witness A P a value\n\
        def extract {A : Type} {P : A -> Type} (a : A) (value : P a) (w : Witness A P a value) : P a := by\n  cases w with\n  | intro x v => exact v\n\
        theorem example : extract 3 true (Witness.intro 3 true : Witness Nat (fun x => Bool) 3 true) = true := by rfl",
    );
}

#[test]
fn index_dependent_proofs_and_values_are_specialized_together() {
    check(&format!(
        "{VEC}\
        theorem proof {{A : Type}} (n : Nat) (xs : Vec A n) (h : n = n) : n = n := by\n  cases xs with\n  | nil => exact h\n  | cons k x tail => exact h\n\
        def other {{A : Type}} (n : Nat) (xs ys : Vec A n) : Vec A n := by\n  cases xs with\n  | nil => exact ys\n  | cons k x tail => exact ys\n\
        theorem example : other 1 (Vec.cons 0 7 Vec.nil) (Vec.cons 0 9 Vec.nil) = Vec.cons 0 9 Vec.nil := by rfl"
    ));
}

#[test]
fn explicit_generalization_keeps_function_valued_indexed_hypotheses() {
    check(&format!(
        "{VEC}\
        theorem general {{A : Type}} (n : Nat) (xs : Vec A n) (m : Nat) : m = m := by\n  induction xs generalizing m with\n  | nil => rfl\n  | cons k x tail ih => exact ih m"
    ));
}

#[test]
fn indexed_cases_cannot_obtain_hidden_induction_hypotheses() {
    let source = format!(
        "{VEC}{LENGTH}\
        theorem bad {{A : Type}} (n : Nat) (xs : Vec A n) : length n xs = n := by\n  cases xs with\n  | nil => rfl\n  | cons k x tail => assumption"
    );
    assert!(
        engine()
            .check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits())
            )
            .is_err()
    );
}

#[test]
fn fixed_repeated_or_let_indices_do_not_become_unconstrained_variables() {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    for suffix in [
        "def bad (xs : Vec Nat 1) : Nat := by cases xs with | nil => exact 0 | cons n x tail => exact x",
        "def bad (n : Nat) (xs : Vec Nat (Nat.succ n)) : Nat := by cases xs with | nil => exact 0 | cons k x tail => exact x",
        "def bad (n : Nat) (xs : Vec Nat n) : Nat := by cases xs with | nil => exact n | cons k x tail => exact n",
    ] {
        let source = format!("{VEC}{suffix}");
        assert!(
            !matches!(
                base.check_source_files(
                    &[source.as_bytes()],
                    &KVMap::new(),
                    SourceCheckLimits::new(limits())
                ),
                Ok(Outcome::Complete(_))
            ),
            "{source}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
    }
    for source in [
        "inductive Same : Nat -> Nat -> Type where | mk (n : Nat) : Same n n\ndef bad (n : Nat) (x : Same n n) : Nat := by cases x with | mk k => exact k",
        "inductive Tagged (tag : Nat) : Nat -> Type where | mk : Tagged tag tag\ndef bad (n : Nat) (x : Tagged n n) : Nat := by cases x with | mk => exact 0",
    ] {
        assert!(
            !matches!(
                base.check_source_files(
                    &[source.as_bytes()],
                    &KVMap::new(),
                    SourceCheckLimits::new(limits())
                ),
                Ok(Outcome::Complete(_))
            ),
            "{source}"
        );
    }
}

#[test]
fn bad_indexed_branches_leave_no_published_prefix_and_recovery_works() {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    let prefix = format!("{VEC}{COPY}");
    let good = "theorem good {A : Type} (n : Nat) (xs : Vec A n) : xs = xs := by cases xs with | nil => rfl | cons k x tail => rfl";
    for suffix in [
        "theorem bad (n : Nat) (xs : Vec Nat n) : n = 0 := by cases xs with | nil => rfl | cons k x tail => rfl",
        "def bad (n : Nat) (xs : Vec Nat n) : Nat := by cases xs with | nil => exact (true : Nat) | cons k x tail => exact x",
        "def bad (n : Nat) (xs : Vec Nat n) : Nat := by cases xs with | nil => exact x | cons k x tail => exact x",
    ] {
        assert!(
            base.check_source_files(
                &[prefix.as_bytes(), suffix.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits())
            )
            .is_err(),
            "{suffix}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
        assert!(matches!(
            base.check_source_files(
                &[prefix.as_bytes(), good.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits())
            ),
            Ok(Outcome::Complete(_))
        ));
    }
}

#[test]
fn dependent_indexed_branches_preserve_lets_and_nested_contexts() {
    check(&format!(
        "{VEC}\
        def remembered {{A : Type}} (n : Nat) (xs : Vec A n) : Nat := let saved := n; by\n  cases xs with\n  | nil => exact saved\n  | cons k x tail => exact saved\n\
        theorem example : remembered 1 (Vec.cons 0 7 Vec.nil) = 1 := by rfl"
    ));
    check(&format!(
        "{VEC}\
        theorem self {{A : Type}} (n m : Nat) (xs : Vec A n) (ys : Vec A m) : n = n := by\n  cases xs with\n  | nil => rfl\n  | cons k x tail =>\n    cases ys with\n    | nil => rfl\n    | cons j y rest => rfl"
    ));
}

#[test]
fn indexed_elimination_resource_stops_preserve_the_original_environment() {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    let mut low = SourceCheckLimits::new(limits());
    low.admission.kernel = low.admission.kernel.narrowed(0, 32);
    let source = format!("{VEC}{COPY}");
    match base.check_source_files(&[source.as_bytes()], &KVMap::new(), low) {
        Ok(Outcome::Inconclusive(_)) => {}
        Err(error) => assert!(
            matches!(error.disposition(), ("resource" | "inconclusive", false, 3)),
            "{error:?}"
        ),
        other => panic!("expected a typed nonanswer, got {other:?}"),
    }
    assert_eq!(base.logical_root(&KVMap::new()), root);
}
