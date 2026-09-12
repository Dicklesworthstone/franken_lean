//! Constrained-index induction must generalize the original major in its motive.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};
fn check(source: &str) {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap();
    engine
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        )
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap();
}
const LOOP: &str = "inductive Loop : Nat -> Type where | seed (n : Nat) : Loop n | step (n : Nat) (rest : Loop n) : Loop n\n\
    def copy (n : Nat) (x : Loop n) : Loop n := match x with | .seed k => Loop.seed k | .step k rest => Loop.step k (copy k rest)\n";
#[test]
fn fixed_index_induction_has_a_genuine_child_hypothesis() {
    check(&format!(
        r#"{LOOP}
theorem copied (x : Loop 7) : copy 7 x = x := by
  induction x with
  | seed n => rfl
  | step n rest ih => simp only [copy, ih rest (HEq.refl 7) (HEq.refl rest)]"#
    ));
}
#[test]
fn impossible_indexed_input_needs_no_induction_alternatives() {
    check(
        "inductive Diagonal : Nat -> Nat -> Type where | mk (n : Nat) : Diagonal n n\n\
        def empty (x : Diagonal 0 1) : Nat := by induction x",
    );
}

#[test]
fn repeated_indices_support_a_recursive_copy_proof() {
    check(
        r#"
inductive PairAt : Nat -> Nat -> Type where
  | leaf (a b : Nat) : PairAt a b
  | step (a b : Nat) (child : PairAt a b) : PairAt a b
def copyPair (a b : Nat) (value : PairAt a b) : PairAt a b := match value with
  | .leaf x y => PairAt.leaf x y
  | .step x y child => PairAt.step x y (copyPair x y child)
theorem repeat_copy (n : Nat) (value : PairAt n n) : copyPair n n value = value := by
  induction value with
  | leaf a b => rfl
  | step a b child ih => simp only [copyPair, ih child (HEq.refl n) (HEq.refl n) (HEq.refl child)]
"#,
    );
}

#[test]
fn shared_parameter_indices_keep_the_parameter_fixed() {
    check(
        r#"
inductive Marked (tag : Nat) : Nat -> Type where
  | base : Marked tag tag
  | step (child : Marked tag tag) : Marked tag tag
def copyMarked (tag n : Nat) (value : Marked tag n) : Marked tag n := match value with
  | .base => Marked.base
  | .step child => Marked.step (copyMarked tag tag child)
theorem marked_copy (tag : Nat) (value : Marked tag tag) : copyMarked tag tag value = value := by
  induction value with
  | base => rfl
  | step child ih => simp only [copyMarked, ih child (HEq.refl tag) (HEq.refl child)]
"#,
    );
}

#[test]
fn dependent_index_telescopes_produce_correct_child_hypotheses() {
    check(
        r#"
inductive Trace (A : Type) (P : A -> Type) : forall a : A, P a -> Type where
  | base (a : A) (v : P a) : Trace A P a v
  | step (a : A) (v : P a) (child : Trace A P a v) : Trace A P a v
def traceCopy {A : Type} {P : A -> Type} (a : A) (v : P a) (t : Trace A P a v) : Trace A P a v := match t with
  | .base x y => Trace.base x y
  | .step x y child => Trace.step x y (traceCopy x y child)
theorem trace_copy (A : Type) (P : A -> Type) (f : A -> A) (a : A) (v : P (f a))
    (value : Trace A P (f a) v) : traceCopy (f a) v value = value := by
  induction value with
  | base x y => rfl
  | step x y child ih =>
    simp only [traceCopy, ih child (HEq.refl (f a)) (HEq.refl v) (HEq.refl child)]
    rfl
"#,
    );
}

#[test]
fn explicit_generalization_allows_changing_accumulators() {
    check(&format!(
        r#"{LOOP}
theorem generalized (x : Loop 7) (acc : Nat) : copy 7 x = x := by
  induction x generalizing acc with
  | seed n => rfl
  | step n rest ih => simp only [copy, ih rest (acc + 1) (HEq.refl 7) (HEq.refl rest)]
"#
    ));
}

const VEC: &str = "inductive Vec (A : Type) : Nat -> Type where | nil : Vec A 0 | cons (n : Nat) (head : A) (tail : Vec A n) : Vec A (Nat.succ n)\n";
#[test]
fn positive_length_induction_uses_conditional_hypotheses_at_the_child_index() {
    check(&format!(
        r#"{VEC}
def length (n : Nat) (xs : Vec Nat n) : Nat := match xs with
  | .nil => 0
  | .cons k x tail => Nat.succ (length k tail)
theorem length_positive (n : Nat) (xs : Vec Nat (Nat.succ n)) : length (Nat.succ n) xs = Nat.succ n := by
  induction xs generalizing n with
  | cons k x tail ih =>
    cases k with
    | zero =>
      cases tail with
      | nil => rfl
    | succ j =>
      simp only [length, ih j tail (HEq.refl (Nat.succ j)) (HEq.refl tail)]
"#
    ));
}

#[test]
fn proof_dependent_hypotheses_and_let_values_survive_generalization() {
    check(&format!(
        r#"{LOOP}
theorem retained (x : Loop 7) (h : x = x) (P : x = x -> Prop) (hp : P h) : P h := by
  induction x with
  | seed n => exact hp
  | step n rest ih => exact hp
def remembered (x : Loop 7) : Nat := let original := x; by
  induction x with
  | seed n => exact n
  | step n rest ih => exact ih rest (HEq.refl 7) (HEq.refl rest)
theorem remembered_ok : remembered (Loop.step 7 (Loop.seed 7)) = 7 := by rfl
"#
    ));
}

#[test]
fn small_elimination_induction_can_produce_proofs() {
    check(
        r#"
inductive Holds : Nat -> Prop where
  | base : Holds 0
  | step (previous : Holds 0) : Holds 0
theorem duplicate (h : Holds 0) : Holds 0 := by
  induction h with
  | base => exact Holds.base
  | step previous ih => exact Holds.step (ih previous (HEq.refl 0) (HEq.refl previous))
"#,
    );
}

fn reject(source: &str) {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap();
    let root = engine.logical_root(&KVMap::new());
    assert!(
        engine
            .check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits)
            )
            .is_err(),
        "unexpected acceptance: {source}"
    );
    assert_eq!(engine.logical_root(&KVMap::new()), root);
}

#[test]
fn induction_does_not_assume_the_whole_equals_its_child() {
    reject(&format!(
        r#"{LOOP}
theorem false_statement (x : Loop 7) : x = Loop.seed 7 := by
  induction x with
  | seed n => rfl
  | step n rest ih => exact ih rest (HEq.refl 7) (HEq.refl rest)
"#
    ));
}

#[test]
fn incompatible_child_indices_remain_real_hypothesis_premises() {
    reject(&format!(
        r#"{VEC}
theorem false_length (xs : Vec Nat 1) : 0 = 1 := by
  induction xs with
  | cons k x tail ih => exact ih tail (HEq.refl 1) (HEq.refl tail)
"#
    ));
}

#[test]
fn cases_cannot_use_the_new_induction_hypotheses() {
    reject(&format!(
        r#"{LOOP}
theorem copied (x : Loop 7) : copy 7 x = x := by
  cases x with
  | seed n => rfl
  | step n rest ih => simp only [copy, ih]
"#
    ));
}

#[test]
fn unknown_indices_and_bad_branches_are_not_discarded() {
    for body in [
        "theorem bad (x : Loop 7) : 0 = 1 := by induction x with | seed n => rfl | step n rest ih => assumption",
        "theorem bad (x : Loop 7) : x = x := by induction x with | seed n => rfl",
        "theorem bad (x : Loop 7) : x = x := by induction x with | seed n => rfl | step n rest ih => exact (true : x = x)",
        "theorem bad (x : Loop 7) : x = x := by induction x generalizing x with | seed n => rfl | step n rest ih => rfl",
        "theorem bad (x : Loop 7) (n : Nat) : x = x := by induction x generalizing n n with | seed k => rfl | step k rest ih => rfl",
    ] {
        reject(&format!("{LOOP}{body}"));
    }
    reject(
        "inductive Tags : Nat -> Type where | zero : Tags 0 | one : Tags 1\n\
        def bad (f : Nat -> Nat) (x : Tags (f 7)) : Nat := by induction x with | zero => exact 0",
    );
}

#[test]
fn constrained_induction_cannot_extract_propositional_payloads() {
    reject(
        r#"
inductive HasData (A : Type) : Nat -> Prop where
  | base (a : A) : HasData A 0
  | step (previous : HasData A 0) : HasData A 0
def extract (A : Type) (h : HasData A 0) : A := by
  induction h with
  | base a => exact a
  | step previous ih => exact ih previous (HEq.refl 0) (HEq.refl previous)
"#,
    );
}

#[test]
fn multiple_recursive_children_have_separate_conditional_hypotheses() {
    check(
        r#"
inductive TreeAt : Bool -> Type where
  | leaf (tag : Bool) : TreeAt tag
  | node (tag : Bool) (left right : TreeAt tag) : TreeAt tag
def mirror (tag : Bool) (tree : TreeAt tag) : TreeAt tag := match tree with
  | .leaf value => TreeAt.leaf value
  | .node value left right => TreeAt.node value (mirror value right) (mirror value left)
theorem twice (tree : TreeAt true) : mirror true (mirror true tree) = tree := by
  induction tree with
  | leaf tag => rfl
  | node tag left right ihl ihr => simp only [mirror, ihl left (HEq.refl true) (HEq.refl left), ihr right (HEq.refl true) (HEq.refl right)]
"#,
    );
}

#[test]
fn branch_names_shadow_original_locals_without_changing_core_identity() {
    check(&format!(
        r#"{LOOP}
theorem shadow (x : Loop 7) (rest : Nat) (ih : Nat) : copy 7 x = x := by
  induction x with
  | seed n => rfl
  | step n rest ih => simp only [copy, ih rest (HEq.refl 7) (HEq.refl rest)]
"#
    ));
}

#[test]
fn unused_annotations_and_supplied_impossible_alternatives_still_reject() {
    reject(&format!(
        r#"{VEC}
def bad (xs : Vec Nat 1) : Nat := by
  induction xs with
  | nil => exact (true : Nat)
  | cons k x rest ih => exact x
"#
    ));
    reject(&format!(
        r#"{LOOP}
theorem bad (x : Loop 7) : copy 7 x = x := by
  induction x with
  | seed n => rfl
  | step n rest ih => exact (let unused := (true : Nat); ih rest (HEq.refl 7) (HEq.refl rest))
"#
    ));
}

#[test]
fn low_budgets_and_bad_file_suffixes_preserve_the_original_environment() {
    use fln::Outcome;
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap();
    let engine = engine
        .check_source_files(
            &[LOOP.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine;
    let root = engine.logical_root(&KVMap::new());
    let good = "theorem good (x : Loop 7) : copy 7 x = x := by\n  induction x with\n  | seed n => rfl\n  | step n rest ih => simp only [copy, ih rest (HEq.refl 7) (HEq.refl rest)]";
    let bad = "theorem bad (x : Loop 7) : 0 = 1 := by\n  induction x with\n  | seed n => rfl\n  | step n rest ih => assumption";
    let mut low = SourceCheckLimits::new(limits);
    low.admission.kernel = low.admission.kernel.narrowed(0, 32);
    match engine.check_source_files(&[good.as_bytes()], &KVMap::new(), low) {
        Ok(Outcome::Inconclusive(_)) => {}
        Err(error) => assert!(
            matches!(error.disposition(), ("resource" | "inconclusive", false, 3)),
            "{error:?}"
        ),
        other => panic!("expected a resource nonanswer, got {other:?}"),
    }
    for valid in [false, true, false, true] {
        let sources = if valid {
            vec![good.as_bytes()]
        } else {
            vec![good.as_bytes(), bad.as_bytes()]
        };
        let result =
            engine.check_source_files(&sources, &KVMap::new(), SourceCheckLimits::new(limits));
        assert_eq!(
            matches!(result, Ok(Outcome::Complete(_))),
            valid,
            "{result:?}"
        );
        assert_eq!(engine.logical_root(&KVMap::new()), root);
    }
}
