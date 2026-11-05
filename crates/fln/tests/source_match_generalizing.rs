//! Explicit match generalization changes the branch context, not just syntax.
//! Positive and negative pairs were checked against the SUITE.lock executable;
//! the Prelude-shaped proofs are ordinary candidates checked by both kernels.
#![forbid(unsafe_code)]

use fln::{
    Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, Name, SourceCheckLimits,
    VmExit,
};
use fln_env::constants::ConstantInfo;

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}

fn engine() -> Engine {
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}

fn checked(base: &Engine, source: &str) -> Engine {
    base.check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits()),
    )
    .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
    .into_complete()
    .expect("the match and every branch pass both checkers")
    .engine
}

fn rejected(base: &Engine, source: &str) {
    let root = base.logical_root(&KVMap::new());
    assert!(
        base.check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .is_err(),
        "{source}"
    );
    assert_eq!(base.logical_root(&KVMap::new()), root);
}

#[test]
fn false_does_not_refine_a_dependent_hypothesis_that_true_and_default_generalize() {
    // SourceSeed omits Bool.noConfusion. Establish the disjoint-constructor
    // fact by ordinary checked source before exercising the branch contexts.
    let base = checked(
        &engine(),
        "theorem falseNeTrue (h : false = true) : False := by contradiction",
    );
    for annotation in ["", "(generalizing := true)"] {
        checked(
            &base,
            &format!(
                r#"
def refineProof (b : Bool) (h : b = true) : Nat :=
  match {annotation} b with
  | true => 1
  | false => False.elim (falseNeTrue h)
"#
            ),
        );
    }
    rejected(
        &base,
        r#"
def invalidRefinement (b : Bool) (h : b = true) : Nat :=
  match (generalizing := false) b with
  | true => 1
  | false => False.elim (falseNeTrue h)
"#,
    );
}

#[test]
fn false_retains_captured_let_dependencies_that_true_and_default_cannot_replace() {
    let base = engine();
    checked(
        &base,
        r#"
def retainProof (b : Bool) (h : b = true) : Nat :=
  let consume : b = true -> Nat := fun _ => 0
  match (generalizing := false) b with
  | true => consume h
  | false => consume h
theorem retained : retainProof true rfl = 0 := by rfl
"#,
    );
    for annotation in ["", "(generalizing := true)"] {
        rejected(
            &base,
            &format!(
                r#"
def invalidCapture (b : Bool) (h : b = true) : Nat :=
  let consume : b = true -> Nat := fun _ => 0
  match {annotation} b with
  | true => consume h
  | false => consume h
"#
            ),
        );
    }
}

// Establish the prerequisites by ordinary checked source, because SourceSeed
// does not ship all of Prelude's decision lemmas. The three target proof bodies
// then retain the exact match/generalizing structure used by Init/Prelude.
const PRELUDE: &str = r#"
namespace MatchPrelude
theorem absurd {p q : Prop} (h : p) (hn : Not p) : q := False.elim (hn h)
theorem ne_true_of_eq_false {b : Bool} (h : b = false) : Not (b = true) := by
  intro ht
  subst h
  contradiction
theorem ne_false_of_eq_true {b : Bool} (h : b = true) : Not (b = false) := by
  intro hf
  subst h
  contradiction
theorem decide_eq_true {p : Prop} [inst : Decidable p] (h : p) : decide p = true :=
  match inst with
  | Decidable.isTrue _ => rfl
  | Decidable.isFalse hn => absurd h hn
theorem decide_eq_false {p : Prop} [inst : Decidable p] (hn : Not p) : decide p = false :=
  match inst with
  | Decidable.isTrue h => absurd h hn
  | Decidable.isFalse _ => rfl
theorem of_decide_eq_true {p : Prop} [inst : Decidable p] : decide p = true -> p := fun h =>
  match (generalizing := false) inst with
  | Decidable.isTrue h1 => h1
  | Decidable.isFalse h1 => absurd h (ne_true_of_eq_false (decide_eq_false h1))
theorem of_decide_eq_false {p : Prop} [inst : Decidable p] : decide p = false -> Not p := fun h =>
  match (generalizing := false) inst with
  | Decidable.isTrue h1 => absurd h (ne_false_of_eq_true (decide_eq_true h1))
  | Decidable.isFalse h1 => h1
theorem of_decide_eq_self_eq_true {A : Type} [inst : DecidableEq A] (a : A) :
    decide (a = a) = true :=
  match (generalizing := false) inst a a with
  | Decidable.isTrue _ => rfl
  | Decidable.isFalse h1 => absurd rfl h1
end MatchPrelude
"#;

#[test]
fn prelude_decision_evidence_proofs_keep_the_original_instance_and_computed_discriminant() {
    let result = checked(&engine(), PRELUDE);
    for name in [
        "of_decide_eq_true",
        "of_decide_eq_false",
        "of_decide_eq_self_eq_true",
    ] {
        let name = Name::from_components(["MatchPrelude", name]);
        let Some(ConstantInfo::Thm(theorem)) = result.environment().find(&name) else {
            panic!("missing checked theorem {name:?}");
        };
        assert!(!theorem.value.has_fvar());
        assert!(!theorem.value.has_expr_mvar());
        assert!(!theorem.value.has_level_mvar());
    }
    checked(
        &result,
        r#"
theorem recoveredTruth : True := MatchPrelude.of_decide_eq_true rfl
theorem recoveredNegation : Not False := MatchPrelude.of_decide_eq_false rfl
theorem checkedSelf (n : Nat) : decide (n = n) = true :=
  MatchPrelude.of_decide_eq_self_eq_true n
"#,
    );
    rejected(
        &result,
        "theorem impossible : False := MatchPrelude.of_decide_eq_true rfl",
    );
}

#[test]
fn computed_discriminants_instantiate_inferred_arguments_before_motive_abstraction() {
    let base = engine();
    checked(
        &base,
        r#"
theorem computedSelf {A : Type} [DecidableEq A] (a : A) :
    @decide (a = a) (decEq a a) = true :=
  match (generalizing := false) decEq a a with
  | Decidable.isTrue _ => rfl
  | Decidable.isFalse h => False.elim (h rfl)
"#,
    );
    rejected(
        &base,
        r#"
theorem invalidComputedSelf {A : Type} [DecidableEq A] (a : A) :
    @decide (a = a) (decEq a a) = false :=
  match (generalizing := false) decEq a a with
  | Decidable.isTrue _ => rfl
  | Decidable.isFalse h => False.elim (h rfl)
"#,
    );
}

#[test]
fn annotated_matches_execute_and_replay_their_selected_branches() {
    let result = engine()
        .execute_source_definitions(
            &[br#"
def select (b : Bool) : Nat :=
  match (generalizing := false) b with
  | true => 11
  | false => 19
def retainProof (b : Bool) (h : b = true) : Nat :=
  let consume : b = true -> Nat := fun _ => 7
  match (generalizing := false) b with
  | true => consume h
  | false => consume h
def pair (a b : Bool) : Nat :=
  match (generalizing := true) a, b with
  | true, true => 1
  | true, false => 2
  | false, true => 3
  | false, false => 4
#eval select true
#eval select false
#eval retainProof true rfl
#eval pair false true
"#],
            &KVMap::new(),
            EngineExecutionLimits::new(limits().kernel),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(result.executions.len(), 7);
    assert_eq!(result.source_evaluation_indices, [3, 4, 5, 6]);
    for (index, expected) in result
        .source_evaluation_indices
        .iter()
        .zip(["11", "19", "7", "3"])
    {
        let execution = &result.executions[*index];
        let VmExit::Returned(value) = &execution.exit else {
            panic!("normal result")
        };
        assert_eq!(
            fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
            Some(expected)
        );
        let replay =
            fln::execute_flbc_artifact(&execution.flbc_artifact, &KVMap::new(), Default::default())
                .unwrap()
                .into_complete()
                .unwrap();
        let VmExit::Returned(value) = replay else {
            panic!("normal replay")
        };
        assert_eq!(
            fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
            Some(expected)
        );
    }
}

#[test]
fn malformed_or_unsupported_annotations_are_never_discarded() {
    let base = engine();
    for source in [
        "def bad (b : Bool) : Nat := match (generalizing := 0) b with | true => 1 | false => 2",
        "def bad (b : Bool) : Nat := match (generalizing := false false) b with | true => 1 | false => 2",
        "def bad (b : Bool) : Nat := match (generalizing := false) h : b with | true => 1 | false => 2",
        "def bad (a b : Bool) : Nat := match (generalizing := false) a, b with | true, true => 1 | _, _ => 2",
    ] {
        rejected(&base, source);
    }
}
