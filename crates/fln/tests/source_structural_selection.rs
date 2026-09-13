//! Structural candidate search must check the whole program at each candidate.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};
fn check(source: &str) {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap()
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        )
        .unwrap_or_else(|e| panic!("{source}\n{e:?}"))
        .into_complete()
        .unwrap();
}
fn reject(source: &str) {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap();
    let before = engine.logical_root(&KVMap::new());
    assert!(
        engine
            .check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits)
            )
            .is_err(),
        "{source}"
    );
    assert_eq!(engine.logical_root(&KVMap::new()), before);
}
#[test]
fn equations_select_the_second_input_instead_of_a_boolean() {
    check(
        "def count : Bool -> Nat -> Nat\n | b, .zero => 0\n | b, .succ n => Nat.succ (count b n)\n theorem computed : count true 9 = 9 := by rfl",
    );
}
#[test]
fn source_match_selects_a_later_parameter_with_original_argument_order() {
    check(
        "def count (b : Bool) (n : Nat) : Nat := match b, n with\n | true, .zero => 0\n | false, .zero => 0\n | b, .succ k => Nat.succ (count b k)\n theorem computed : count false 8 = 8 := by rfl",
    );
}
#[test]
fn a_recursive_but_unchanged_earlier_argument_is_not_the_decreasing_one() {
    check(
        "def add : Nat -> Nat -> Nat\n | x, .zero => x\n | x, .succ n => Nat.succ (add x n)\n theorem computed : add 4 7 = 11 := by rfl",
    );
}
#[test]
fn a_third_candidate_keeps_generic_payloads_and_partial_applications() {
    check(
        "def retain {A : Type} : A -> Bool -> Nat -> Nat -> A\n | a, b, .zero, acc => a\n | a, b, .succ n, acc => let smaller := retain a b n; smaller (acc + 1)\n theorem computed : retain 17 false 4 9 = 17 := by rfl",
    );
}
#[test]
fn ordinary_proof_scripts_cannot_access_candidate_recursion_hypotheses() {
    reject(
        "theorem bad : Bool -> Nat -> (0 = 0) | b, .zero => rfl | b, .succ n => let ignored := (fun (p : 0 = 0) => 0) (bad b n); by assumption",
    );
}
#[test]
fn neither_changing_candidate_can_license_calls_on_the_original_input() {
    for body in [
        "def bad : Nat -> Nat -> Nat | .zero, .zero => 0 | .zero, .succ b => bad 0 b | .succ a, .zero => bad a 0 | .succ a, .succ b => bad (Nat.succ a) (Nat.succ b)",
        "def bad : Bool -> Nat -> Nat | b, .zero => 0 | b, .succ n => let unused := bad b (Nat.succ n); 0",
        "def bad : Bool -> Nat -> Nat | b, .zero => 0 | b, .succ n => bad",
    ] {
        reject(body);
    }
}
#[test]
fn candidate_retry_never_erases_bad_annotations_in_other_columns_or_rows() {
    for source in [
        "def bad : Bool -> Nat -> Nat | b, .zero => 0 | b, .succ n => let unused := (1 : String); bad b n",
        "def bad (b : Bool) (n : Nat) : Nat := match (1 : String), n with | _, .zero => 0 | _, .succ k => bad b k",
    ] {
        reject(source);
    }
}

#[test]
fn later_indexed_discriminants_refine_the_actual_child_indices() {
    check(
        "inductive Vec (A : Type) : Nat -> Type where | nil : Vec A 0 | cons (n : Nat) (head : A) (tail : Vec A n) : Vec A (Nat.succ n)\n\
      def copy {A : Type} (tag : Bool) (n : Nat) (xs : Vec A n) : Vec A n := match tag, xs with\n\
       | _, .nil => Vec.nil\n\
       | b, .cons k x tail => Vec.cons k x (copy b k tail)\n\
      theorem copied : copy false 1 (Vec.cons 0 9 Vec.nil) = Vec.cons 0 9 Vec.nil := by rfl",
    );
}
#[test]
fn proof_of_equation_defined_recursion_uses_the_selected_recursor() {
    check(
        "def copy : Bool -> Nat -> Nat | b, .zero => 0 | b, .succ k => Nat.succ (copy b k)
      theorem same (b : Bool) (n : Nat) : copy b n = n := by
        induction n with
        | zero => rfl
        | succ k ih => simp only [copy, ih]",
    );
}
#[test]
fn candidate_search_preserves_first_matching_row_priority() {
    check(
        "def f : Bool -> Nat -> Nat | true, _ => 11 | false, .zero => 7 | false, .succ k => Nat.succ (f false k)\n\
      theorem first : f true 6 = 11 := by rfl\n theorem next : f false 3 = 10 := by rfl",
    );
}

#[test]
fn matched_accumulators_before_the_decreasing_parameter_may_change() {
    check(
        "def count : Nat -> Nat -> Nat | acc, .zero => acc | acc, .succ k => count (acc + 1) k\n theorem computed : count 4 7 = 11 := by rfl",
    );
}
