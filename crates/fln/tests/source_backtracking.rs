//! Real source backtracking restores all semantic state, never spent work.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};

fn run(source: &str) -> Result<Engine, String> {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap();
    let root = engine.logical_root(&KVMap::new());
    let result = engine.check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits),
    );
    assert_eq!(engine.logical_root(&KVMap::new()), root);
    result
        .map_err(|e| format!("{e:?}"))?
        .into_complete()
        .map(|r| r.engine)
        .map_err(|e| format!("{e:?}"))
}
fn check(source: &str) {
    run(source).unwrap_or_else(|e| panic!("{source}\n{e}"));
}
fn reject(source: &str) {
    assert!(run(source).is_err(), "accepted {source}");
}
const BOTH: &str = "inductive Both (P Q : Prop) : Prop where | intro (left : P) (right : Q)\n";
const PACKAGE: &str = "structure Package where\n carrier : Type\n value : carrier\n";

#[test]
fn first_uses_the_first_success_not_the_first_complete_proof() {
    check(&format!(
        "{BOTH}theorem t (P : Prop) (p : P) : Both P P := by\n first | constructor | fail\n all_goals exact p"
    ));
    check(
        "def choice : Nat := by first | exact 3 | exact 7\ntheorem chosen : choice = 3 := by rfl",
    );
    reject(&format!(
        "{BOTH}theorem t (P : Prop) (p : P) : Both P P := by\n first | constructor | exact Both.intro p p\n fail"
    ));
}
#[test]
fn rigid_reflexivity_and_exact_failures_can_try_the_next_proof() {
    check("theorem t (n m : Nat) (h : n = m) : n = m := by first | rfl | exact h");
    check("theorem t : 0 = 0 := by first | exact 1 | rfl");
    check("theorem t : 0 = 0 := by first | exact missing | rfl");
    reject("theorem t : 0 = 1 := by first | rfl | exact missing");
}
#[test]
fn try_restores_partial_introductions_and_local_definitions() {
    check(
        "theorem t (P : Prop) : P -> P := by\n try (intro lost; fail)\n intro retained\n exact retained",
    );
    reject("theorem t (P : Prop) : P -> P := by\n try (intro lost; fail)\n exact lost");
    check("theorem t (P : Prop) (p : P) : P := by\n try (have local := p; fail)\n exact p");
    reject("theorem t (P : Prop) (p : P) : P := by\n try (have local := p; fail)\n exact local");
}
#[test]
fn failed_alternatives_undo_dependent_carrier_assignments() {
    check(&format!(
        "{PACKAGE}def packed : Package := by\n refine Package.mk ?carrier ?value\n first\n | (exact Nat; fail)\n | exact String\n exact \"kept\"\ntheorem value : packed.value = \"kept\" := by rfl"
    ));
}
#[test]
fn failure_after_solving_all_goals_rolls_back_the_proof() {
    check(
        "def chosen : Nat := by first | (exact 7; fail) | exact 9\ntheorem result : chosen = 9 := by rfl",
    );
    check("theorem t : 0 = 0 := by\n try (rfl; fail)\n rfl");
}
#[test]
fn alternatives_can_map_over_all_current_goals() {
    check(&format!(
        "{BOTH}theorem t (P Q : Prop) (p : P) (q : Q) : Both P Q := by\n constructor\n first | (all_goals exact p) | (all_goals assumption)"
    ));
}
#[test]
fn successful_nested_choices_do_not_commit_the_enclosing_choice() {
    check(
        "def t : Nat := by first | (first | exact 1 | exact 2; fail) | exact 3\ntheorem result : t = 1 := by rfl",
    );
    check(
        "def t : Nat := by first | ((first | exact 1 | exact 2); fail) | exact 3\ntheorem result : t = 3 := by rfl",
    );
}
#[test]
fn try_and_choices_inside_bullets_preserve_siblings() {
    check(&format!(
        "{BOTH}theorem t (P Q : Prop) (p : P) (q : Q) : Both P Q := by\n constructor\n · first | exact q | exact p\n · try exact p\n   exact q"
    ));
    reject(&format!(
        "{BOTH}theorem t (P : Prop) (p : P) : Both P P := by\n constructor\n · first | skip | exact p\n · exact p"
    ));
}
#[test]
fn failed_focus_and_sequencing_restore_their_entire_continuation() {
    check(&format!(
        "{BOTH}theorem t (P Q : Prop) (p : P) (q : Q) : Both P Q := by\n first | (constructor <;> exact p) | (constructor <;> assumption)"
    ));
    check(&format!(
        "{BOTH}theorem t (P Q : Prop) (p : P) (q : Q) : Both P Q := by\n try (focus (constructor; exact p); fail)\n constructor\n exact p\n exact q"
    ));
}
#[test]
fn shared_synthetic_holes_are_restored_after_failure() {
    check(&format!(
        "{BOTH}theorem t (P : Prop) (p : P) : Both P P := by\n refine Both.intro ?same ?same\n first | (exact p; fail) | exact p"
    ));
}
#[test]
fn nested_local_proofs_can_fail_back_to_an_enclosing_alternative() {
    check(
        "theorem t : 0 = 0 := by\n first\n | have h : 0 = 0 := by\n     first | fail | rfl\n   exact h\n | fail",
    );
    check(
        "theorem t : 0 = 0 := by\n first\n | have h : 0 = 0 := by\n     fail\n   exact h\n | rfl",
    );
}
#[test]
fn substitutions_in_failed_alternatives_do_not_escape() {
    check("theorem t (n m : Nat) (h : n = m) : n = m := by\n try (subst h; fail)\n exact h");
}
#[test]
fn no_goal_controls_obey_success_and_failure() {
    check("theorem t : 0 = 0 := by\n rfl\n try fail\n first | fail | skip\n all_goals fail");
    reject("theorem t : 0 = 0 := by\n rfl\n first | fail | exact missing");
}
#[test]
fn unchosen_match_coverage_does_not_execute_but_chosen_rows_are_checked() {
    check(
        "theorem t : 0 = 0 := by\n first\n | rfl\n | have fn : Bool -> Nat := fun | true => 1 | false => 2\n   rfl",
    );
    check(
        "theorem t : 0 = 0 := by\n first\n | have fn : Bool -> Nat := fun | true => 1 | false => 2\n   fail\n | rfl",
    );
    reject(
        "def t : Nat := by\n first\n | exact (match true, false with | _, _ => 7 | true, _ => 9)\n | fail",
    );
}
#[test]
fn failed_attempts_do_not_hide_obligations_in_successful_attempts() {
    reject("theorem t : 0 = 0 := by first | (have h : String := 1; rfl) | fail");
    check("theorem t : 0 = 0 := by first | (have h : String := 1; rfl) | rfl");
    reject("def t : Nat := by first | (refine (fun x : Nat => 1) ?_) | exact 1");
}

#[test]
fn nested_attempts_use_flat_driver_checkpoints() {
    for opener in ["try (", "first | fail | ("] {
        check(&format!(
            "theorem t : 0 = 0 := by {}rfl{}",
            opener.repeat(150),
            ")".repeat(150)
        ));
    }
}

#[test]
fn resources_are_not_reinterpreted_as_an_optional_tactic_failure() {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap();
    let root = engine.logical_root(&KVMap::new());
    let source = "theorem t : 0 = 0 := by first | try (first | rfl | fail) | rfl";
    let mut low = SourceCheckLimits::new(limits);
    low.admission.kernel = low.admission.kernel.narrowed(0, 32);
    match engine.check_source_files(&[source.as_bytes()], &KVMap::new(), low) {
        Ok(fln::Outcome::Inconclusive(_)) => {}
        Err(error) => assert!(
            matches!(error.disposition(), ("resource" | "inconclusive", false, 3)),
            "{error:?}"
        ),
        result => panic!("resource stop swallowed: {result:?}"),
    }
    assert_eq!(engine.logical_root(&KVMap::new()), root);
    engine
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        )
        .unwrap()
        .into_complete()
        .unwrap();
}

#[test]
fn selected_scoped_matches_and_induction_keep_their_obligations() {
    check(
        "theorem t (b : Bool) : b = b := by\n first\n | cases b with\n   | false => first | fail | rfl\n   | true => rfl\n | fail",
    );
    check(
        "theorem t (n : Nat) : n = n := by\n first\n | induction n with\n   | zero => rfl\n   | succ k ih => first | exact missing | rfl\n | fail",
    );
    reject(
        "theorem t (b : Bool) : 0 = 1 := by\n first\n | cases b with\n   | false => first | fail | rfl\n   | true => rfl\n | fail",
    );
}
