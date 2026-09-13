//! Synthetic proof holes remain explicit scoped obligations.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};
fn run(source: &str) -> Result<(), String> {
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
        .map_err(|error| format!("{error:?}"))?
        .into_complete()
        .map(|_| ())
        .map_err(|error| format!("{error:?}"))
}
fn check(source: &str) {
    run(source).unwrap_or_else(|error| panic!("{source}\n{error}"));
}
fn reject(source: &str) {
    assert!(run(source).is_err(), "accepted {source}");
}
const BOTH: &str = "inductive Both (P Q : Prop) : Prop where | intro (left : P) (right : Q)\n";
#[test]
fn partial_proof_terms_expose_only_the_requested_holes() {
    check(&format!(
        "{BOTH} theorem pair (P Q : Prop) (p : P) (q : Q) : Both P Q := by refine Both.intro p ?_; exact q"
    ));
    check(&format!(
        "{BOTH} theorem pair (P Q : Prop) (p : P) (q : Q) : Both P Q := by refine Both.intro ?_ ?_; exact p; exact q"
    ));
}
#[test]
fn repeated_named_holes_share_one_goal_in_the_same_scope() {
    check(
        "structure Pair where\n first : Nat\n second : Nat\ndef pair : Pair := by refine Pair.mk ?same ?same; exact 7\ntheorem first : pair.first = 7 := by rfl\ntheorem second : pair.second = 7 := by rfl",
    );
}
#[test]
fn holes_under_lambdas_capture_their_entire_dependent_context() {
    check(
        "def identity : forall A : Type, A -> A := by refine fun A x => ?_; exact x\ntheorem computes : identity Nat 7 = 7 := by rfl",
    );
    check("theorem refl (A : Type) : forall x : A, x = x := by refine fun x => ?_; rfl");
}
#[test]
fn lambda_holes_keep_separate_shadowed_variable_identities() {
    check(
        "structure Pair where\n first : Nat -> Nat\n second : Nat -> Nat\ndef pair : Pair := by refine Pair.mk (fun x => ?_) (fun x => ?_); exact x + 1; exact x + 2\ntheorem first : pair.first 7 = 8 := by rfl\ntheorem second : pair.second 7 = 9 := by rfl",
    );
}
#[test]
fn dependent_holes_schedule_type_and_witness_before_consumers() {
    check(
        "structure Package where\n carrier : Type\n value : carrier\ndef package : Package := by refine Package.mk ?_ ?_; exact Nat; exact 7\ntheorem checked : package.value = 7 := by rfl",
    );
    check(
        "inductive Witness (P : Nat -> Prop) : Prop where | intro (n : Nat) (proof : P n)\ntheorem exists : Witness (fun n => n = 7) := by refine Witness.intro ?w ?p; exact 7; rfl",
    );
}
#[test]
fn refinement_composes_with_intro_constructor_and_nested_local_proofs() {
    check(&format!(
        "{BOTH} theorem nested (P Q : Prop) : P -> Q -> Both P (Both Q P) := by intro p q; refine Both.intro p ?_; constructor; exact q; exact p"
    ));
    check(&format!(
        "{BOTH} theorem local (P : Prop) (p : P) : Both P P := by\n have h : Both P P := by\n  refine Both.intro ?_ ?_\n  exact p\n  exact p\n exact h"
    ));
}
#[test]
fn captured_let_definitions_keep_values_instead_of_becoming_assumptions() {
    check(
        "def selected (n : Nat) : Nat := by let x := n + 1; refine ?_; exact x\ntheorem checked : selected 7 = 8 := by rfl",
    );
    check(
        "def function : Nat -> Nat := by refine fun n => ?_; let x := n + 1; refine ?_; exact x\ntheorem checked : function 7 = 8 := by rfl",
    );
}
#[test]
fn unused_synthetic_holes_are_still_obligations() {
    let prefix = "def ignore (unused : Nat) : 0 = 0 := rfl\n";
    reject(&format!(
        "{prefix} theorem bad : 0 = 0 := by refine ignore ?_"
    ));
    check(&format!(
        "{prefix} theorem good : 0 = 0 := by refine ignore ?_; exact 7"
    ));
    let prefix = "def ignoreProof (unused : 0 = 1) : 0 = 0 := rfl\n";
    reject(&format!(
        "{prefix} theorem bad : 0 = 0 := by refine ignoreProof ?_"
    ));
    reject(&format!(
        "{prefix} theorem bad : 0 = 0 := by refine ignoreProof ?_; rfl"
    ));
}
#[test]
fn unresolved_holes_and_invalid_annotations_never_close_a_declaration() {
    for source in [
        "theorem bad : 0 = 1 := by refine ?_",
        "theorem bad : 0 = 1 := by refine ?_; rfl",
        "def ignore (n : Nat) (h : 0 = 0) : 0 = 0 := h\ntheorem bad : 0 = 0 := by refine ignore (1 : String) ?_; rfl",
        "theorem bad : 0 = 0 := by exact ?_",
        "def bad : Nat := ?_",
        "theorem bad : 0 = 1 := by refine ?self; exact ?self",
    ] {
        reject(source);
    }
}
#[test]
fn named_holes_cannot_capture_another_scope_or_take_incompatible_types() {
    reject(
        "structure Pair where\n first : Nat -> Nat\n second : Nat -> Nat\ndef bad : Pair := by refine Pair.mk (fun x => ?same) (fun y => ?same); exact x",
    );
    reject(
        "structure Pair where\n first : Nat\n second : String\ndef bad : Pair := by refine Pair.mk ?same ?same; exact 7",
    );
}
#[test]
fn implicit_inference_holes_are_not_promoted_to_tactic_goals() {
    check("theorem simple (n : Nat) : n = n := by refine Eq.refl ?_; exact n");
    check(
        "def identity {A : Type} (x : A) : A := x\ntheorem same (n : Nat) : identity n = n := by refine Eq.refl ?_; exact n",
    );
    reject(
        "def ignore (n : Nat) (h : 0 = 0) : 0 = 0 := h\ntheorem bad : 0 = 0 := by refine ignore _ ?_; rfl",
    );
}
#[test]
fn malformed_synthetic_hole_spelling_refuses() {
    for spelling in ["?", "? _", "?7", "?a.b"] {
        reject(&format!("def bad : Nat := by refine {spelling}; exact 7"));
    }
}

#[test]
fn later_explicit_goals_cannot_be_solved_by_inference_or_ignored_by_conversion() {
    reject("theorem bad (n m : Nat) : n = n := by refine Eq.refl ?_; exact m");
    reject("def ignore (n : Nat) : 0 = 0 := rfl\ntheorem bad : 0 = 0 := by refine ignore ?_");
    check("theorem good (n : Nat) : n = n := by refine Eq.refl _");
    reject("theorem extra (n : Nat) : n = n := by refine Eq.refl _; exact n");
}

#[test]
fn holes_in_annotations_are_real_type_obligations() {
    check(
        "def annotated : Nat := by refine (7 : ?_); exact Nat\ntheorem computes : annotated = 7 := by rfl",
    );
    reject("def bad : Nat := by refine (7 : ?_); exact String");
}

#[test]
fn distinct_refinement_frames_do_not_share_named_goals() {
    check(&format!(
        "{BOTH} theorem twice (P : Prop) (p : P) : Both P P := by\n constructor\n refine ?goal\n exact p\n refine ?goal\n exact p"
    ));
    reject(&format!(
        "{BOTH} theorem bad : Both (0 = 0) (0 = 1) := by\n constructor\n refine ?goal\n rfl\n refine ?goal\n rfl"
    ));
}

#[test]
fn branch_scopes_do_not_leak_synthetic_holes_or_local_assumptions() {
    check(
        "theorem same (b : Bool) : b = b := by\n cases b with\n | false =>\n  refine ?same\n  rfl\n | true =>\n  refine ?same\n  rfl",
    );
    reject(
        "theorem bad (b : Bool) : 0 = 0 := by\n cases b with\n | false =>\n  refine ?_\n  have secret : 0 = 0 := rfl\n  exact secret\n | true =>\n  refine ?_\n  exact secret",
    );
}

#[test]
fn dependent_substitution_rebuilds_refined_hole_contexts() {
    check(
        "theorem move (n m : Nat) (h : n = m) (P : Nat -> Prop) (p : P n) : P m := by refine ?_; subst h; exact p",
    );
    check(
        "theorem move (A B : Type) (a : A) (b : B) (h : HEq a b) (P : forall T : Type, T -> Prop) (p : P A a) : P B b := by refine ?_; subst h; exact p",
    );
}

#[test]
fn refinement_holes_preserve_hidden_hypotheses_and_recursion_restrictions() {
    reject(
        "def copy (n : Nat) : Nat := match n with | .zero => 0 | .succ k => Nat.succ (copy k)\ntheorem bad (n : Nat) : copy n = n := by\n cases n with\n | zero => rfl\n | succ k =>\n  refine ?_\n  assumption",
    );
    reject(
        "def bad (n : Nat) : Nat := match n with | .zero => 0 | .succ k => by refine ?_; exact bad n",
    );
    check(
        "def copy (n : Nat) : Nat := match n with | .zero => 0 | .succ k => Nat.succ (copy k)\ntheorem correct (n : Nat) : copy n = n := by\n induction n with\n | zero => rfl\n | succ k ih =>\n  refine ?_\n  simp only [copy, ih]",
    );
}

#[test]
fn irrelevant_ill_typed_arguments_receive_actual_kernel_rejections() {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap();
    let root = engine.logical_root(&KVMap::new());
    for source in [
        "def ignore (n : Nat) (h : 0 = 0) : 0 = 0 := h\ntheorem bad : 0 = 0 := by refine ignore (1 : String) ?_; rfl",
        "def identity (n : Nat) : Nat := n\ntheorem bad (n m : Nat) : identity n = n := by refine Eq.refl ?_; exact m",
    ] {
        let problem = engine
            .check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits),
            )
            .unwrap_err();
        assert!(
            problem.disposition().1,
            "expected K1 rejection, got {problem:?}"
        );
        assert_eq!(engine.logical_root(&KVMap::new()), root);
    }
}

#[test]
fn refinement_exhaustion_and_failure_do_not_publish_a_prefix() {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap();
    let root = engine.logical_root(&KVMap::new());
    let source = "theorem same (n : Nat) : n = n := by refine Eq.refl ?_; exact n";
    let mut low = SourceCheckLimits::new(limits);
    low.admission.kernel = low.admission.kernel.narrowed(0, 32);
    match engine.check_source_files(&[source.as_bytes()], &KVMap::new(), low) {
        Ok(fln::Outcome::Inconclusive(_)) => {}
        Err(error) => assert!(
            matches!(error.disposition(), ("resource" | "inconclusive", false, 3)),
            "{error:?}"
        ),
        other => panic!("expected resource stop, got {other:?}"),
    }
    assert_eq!(engine.logical_root(&KVMap::new()), root);
    for valid in [true, false, true] {
        let suffix = if valid {
            "theorem second : 0 = 0 := by refine ?_; rfl"
        } else {
            "theorem second : 0 = 1 := by refine ?_; rfl"
        };
        let outcome = engine.check_source_files(
            &[source.as_bytes(), suffix.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        );
        assert_eq!(outcome.is_ok(), valid, "{outcome:?}");
        assert_eq!(engine.logical_root(&KVMap::new()), root);
    }
}

#[test]
fn captured_goals_compose_with_function_valued_recursive_constructors() {
    check(
        "inductive Tree where | leaf (value : Nat) | node (children : Nat -> Tree)\ndef generated : Tree := by right; refine fun i => ?_; left; exact i\ntheorem canonical : generated = Tree.node (fun i => Tree.leaf i) := by rfl",
    );
    check(
        "inductive Impossible : Prop where\ninductive Accessible (r : Nat -> Nat -> Prop) : Nat -> Prop where | intro (x : Nat) (children : forall y : Nat, r y x -> Accessible r y) : Accessible r x\ntheorem well : Accessible (fun x y => Impossible) 7 := by constructor; refine fun y h => ?_; cases h",
    );
}
