//! Goal scopes retain obligations, ordering, and branch-local identities.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};
fn run(source: &str) -> Result<(), String> {
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
fn bullets_scope_constructor_subgoals() {
    check(&format!(
        "{BOTH}theorem pair (P Q : Prop) (p : P) (q : Q) : Both P Q := by\n  constructor\n  · exact p\n  · exact q"
    ));
}
#[test]
fn nested_bullets_own_every_descendant_goal() {
    check(&format!(
        "{BOTH}theorem nested (P Q : Prop) (p : P) (q : Q) : Both (Both P Q) P := by\n  constructor\n  · constructor\n    · exact p\n    · exact q\n  · exact p"
    ));
}
#[test]
fn an_unfinished_bullet_cannot_borrow_the_next_bullets_proof() {
    reject(&format!(
        "{BOTH}theorem bad (P : Prop) (p : P) : Both (P -> P) P := by\n  constructor\n  · intro h\n  · exact p\n  exact p"
    ));
}
#[test]
fn focused_tactics_return_their_unsolved_goals_in_order() {
    check(&format!(
        "{BOTH}theorem pair (P Q : Prop) (p : P) (q : Q) : Both (P -> P) Q := by\n  constructor\n  focus intro h\n  exact h\n  exact q"
    ));
    check(&format!(
        "{BOTH}theorem nested (P Q : Prop) (p : P) (q : Q) : Both (Both P Q) P := by\n  constructor\n  focus constructor\n  exact p\n  exact q\n  exact p"
    ));
}
#[test]
fn all_goals_closes_each_original_goal() {
    check(&format!(
        "{BOTH}theorem pair (P : Prop) (p : P) : Both P P := by\n  constructor\n  all_goals assumption"
    ));
}
#[test]
fn all_goals_returns_new_goals_without_mapping_over_them_again() {
    check(&format!(
        "{BOTH}theorem nested (P Q : Prop) (p : P) (q : Q) : Both (Both P Q) (Both Q P) := by\n  constructor\n  all_goals constructor\n  · exact p\n  · exact q\n  · exact q\n  · exact p"
    ));
}
#[test]
fn all_goals_preserves_local_introductions_and_goal_order() {
    check(
        "inductive Product (A B : Type) where | mk (first : A) (second : B)
def functions : Product (Nat -> Nat) (Bool -> Bool) := by\n  constructor\n  all_goals intro x\n  · exact x\n  · exact x"
    );
}
#[test]
fn all_goals_multiline_bodies_run_once_per_goal() {
    check(&format!(
        "{BOTH}theorem functions : Both (forall n : Nat, n = n) (forall b : Bool, b = b) := by\n  constructor\n  all_goals\n    intro x\n    rfl"
    ));
}
#[test]
fn all_goals_cannot_cross_a_scoped_constructor_alternative() {
    check(
        "theorem same (b : Bool) : b = b := by\n  cases b with\n  | false => all_goals rfl\n  | true => rfl",
    );
    reject(
        "theorem bad (b : Bool) : 0 = 0 := by\n  cases b with\n  | false => all_goals rfl\n  | true => intro x",
    );
}
#[test]
fn empty_all_goals_is_vacuous_but_extra_tactics_in_nonempty_scopes_fail() {
    check("theorem same : 0 = 0 := by\n  rfl\n  all_goals rfl");
    check("theorem same : 0 = 0 := by\n  · rfl\n    all_goals rfl");
    reject("theorem bad : 0 = 0 := by\n  focus\n    rfl\n    exact (1 : String)");
    reject("theorem bad : 0 = 0 := by\n  · rfl\n    rfl");
}
#[test]
fn focused_contexts_do_not_export_local_facts_to_siblings() {
    reject(&format!(
        "{BOTH}theorem bad (P : Prop) (p : P) : Both P P := by\n  constructor\n  · have secret := p\n    exact secret\n  · exact secret"
    ));
    check(&format!(
        "{BOTH}theorem pair (P : Prop) (p : P) : Both P P := by\n  constructor\n  all_goals\n    have saved := p\n    exact saved"
    ));
}
#[test]
fn dependent_refinement_goals_keep_their_checked_parent_continuations() {
    check(
        "structure Package where\n carrier : Type\n value : carrier\ndef package : Package := by\n  refine Package.mk ?_ ?_\n  · exact Nat\n  · exact 7\ntheorem result : package.value = 7 := by rfl",
    );
    check(
        "structure Pair where\n first : Nat\n second : Nat\ndef pair : Pair := by\n  refine Pair.mk ?same ?same\n  all_goals exact 9\ntheorem result : pair.second = 9 := by rfl",
    );
}
#[test]
fn false_or_unused_obligations_cannot_escape_scope_control() {
    for tactic in ["·", "focus", "all_goals"] {
        reject(&format!("theorem bad : 0 = 1 := by\n  {tactic} rfl"));
        reject(&format!(
            "theorem bad : 0 = 0 := by\n  {tactic}\n    have unused : String := 1\n    rfl"
        ));
    }
    reject(
        "def ignore (n : Nat) : 0 = 0 := rfl\ntheorem bad : 0 = 0 := by\n  focus refine ignore ?_",
    );
}
#[test]
fn strict_alternatives_inside_focus_still_require_complete_proofs() {
    reject(
        "theorem bad (b : Bool) : Nat -> Nat := by\n  focus\n    cases b with\n    | false => intro x\n    | true => exact (fun x => x)\n  exact x",
    );
}
#[test]
fn nested_local_proofs_and_induction_can_use_goal_controls() {
    check(&format!(
        "{BOTH}theorem pair (n : Nat) : Both (n = n) (n = n) := by\n  have same : n = n := by\n    induction n with\n    | zero => focus rfl\n    | succ k ih =>\n      · rfl\n  constructor\n  all_goals exact same"
    ));
}

#[test]
fn dependent_context_transport_inside_a_bullet_is_not_visible_to_its_sibling() {
    check(&format!(
        "{BOTH}theorem transport (n m : Nat) (h : n = m) (P : Nat -> Prop) (p : P n) : Both (P m) (P n) := by\n  constructor\n  · subst h\n    exact p\n  · exact p"
    ));
}
#[test]
fn goal_control_resource_stops_leave_the_original_engine_reusable() {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap();
    let root = engine.logical_root(&KVMap::new());
    let source =
        format!("{BOTH}theorem t : Both (0 = 0) (0 = 0) := by\n  constructor\n  all_goals rfl");
    let mut constrained = SourceCheckLimits::new(limits);
    constrained.admission.kernel = constrained.admission.kernel.narrowed(0, 32);
    match engine.check_source_files(&[source.as_bytes()], &KVMap::new(), constrained) {
        Ok(fln::Outcome::Inconclusive(_)) => {}
        Err(error) => assert!(
            matches!(error.disposition(), ("resource" | "inconclusive", false, 3)),
            "{error:?}"
        ),
        other => panic!("expected resource stop, got {other:?}"),
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
fn sequencing_maps_only_over_new_descendants() {
    check(&format!(
        "{BOTH}theorem paired (P Q : Prop) (p : P) (q : Q) : Both (Both P P) Q := by\n  constructor\n  constructor <;> exact p\n  exact q"
    ));
}
#[test]
fn sequencing_preserves_the_left_operands_unsolved_main_goal() {
    check(&format!(
        "{BOTH}theorem functions (P Q : Prop) (q : Q) : Both (P -> P) Q := by\n  constructor\n  intro p <;> exact p\n  exact q"
    ));
}
#[test]
fn sequencing_can_leave_new_goals_in_their_original_order() {
    check(&format!(
        "{BOTH}theorem nested (P Q : Prop) (p : P) (q : Q) : Both (Both P Q) (Both Q P) := by\n  constructor <;> constructor\n  · exact p\n  · exact q\n  · exact q\n  · exact p"
    ));
}
#[test]
fn chained_sequencing_maps_each_stage_once() {
    check(&format!(
        "{BOTH}theorem nested (P : Prop) (p : P) : Both (Both P P) (Both P P) := by\n  constructor <;> constructor <;> exact p"
    ));
}
#[test]
fn parenthesized_tactics_preserve_sequential_proof_state() {
    check(&format!(
        "{BOTH}theorem paired (P Q : Prop) (p : P) (q : Q) : Both P Q := by\n  (constructor; exact p; exact q)"
    ));
    check(&format!(
        "{BOTH}theorem paired (P Q : Prop) (p : P) (q : Q) : Both P Q := by\n  (constructor; exact p) <;> exact q"
    ));
}
#[test]
fn sequenced_parenthesized_bodies_own_their_local_facts() {
    check(&format!(
        "{BOTH}theorem paired (P : Prop) (p : P) : Both P P := by\n  constructor <;> (have local := p; exact local)"
    ));
    reject(&format!(
        "{BOTH}theorem bad (P : Prop) (p : P) : Both P P := by\n  constructor\n  (have secret := p; exact secret) <;> rfl\n  exact secret"
    ));
}
#[test]
fn sequencing_in_nested_scopes_respects_constructor_alternative_barriers() {
    check(&format!(
        "{BOTH}theorem paired (b : Bool) : Both (b = b) (b = b) := by\n  cases b with\n  | false => constructor <;> rfl\n  | true => constructor <;> rfl"
    ));
    check(&format!(
        "{BOTH}theorem paired (P : Prop) (p : P) : Both (Both P P) P := by\n  constructor\n  · constructor <;> exact p\n  · exact p"
    ));
}
#[test]
fn unscoped_elimination_descendants_can_be_sequenced() {
    check("theorem same (b : Bool) : b = b := by\n  cases b <;> rfl");
    check("theorem same (n : Nat) : n = n := by\n  induction n <;> rfl");
}
#[test]
fn sequencing_and_all_goals_operate_on_independent_frontiers() {
    check(&format!(
        "{BOTH}theorem paired (P : Prop) (p : P) : Both (Both P P) (Both P P) := by\n  constructor\n  all_goals constructor <;> exact p"
    ));
    check(&format!(
        "{BOTH}theorem paired : Both (forall n : Nat, n = n) (forall b : Bool, b = b) := by\n  constructor <;> (intro x; rfl)"
    ));
}
#[test]
fn refinement_continuations_survive_sequenced_goals() {
    check(
        "structure Pair where\n first : Nat\n second : Nat\ndef pair : Pair := by\n  refine Pair.mk ?shared ?shared <;> exact 7\ntheorem checked : pair.first = 7 := by rfl",
    );
    check(&format!(
        "{BOTH}theorem paired (P : Prop) (p : P) : Both P P := by\n  refine Both.intro ?_ ?_ <;> exact p"
    ));
}
#[test]
fn solved_left_operand_does_not_execute_its_vacuous_continuation() {
    check("theorem same : 0 = 0 := by rfl <;> exact unknown");
    reject("theorem bad : 0 = 1 := by rfl <;> exact unknown");
}
#[test]
fn invalid_obligations_and_failed_descendants_are_not_erased_by_sequencing() {
    reject(&format!(
        "{BOTH}theorem bad : Both (0 = 0) (0 = 1) := by constructor <;> rfl"
    ));
    reject("theorem bad : 0 = 0 := by (have unused : String := 1; rfl) <;> exact unknown");
    reject("theorem bad : 0 = 0 := by (rfl; exact unknown) <;> rfl");
    reject(&format!(
        "{BOTH}theorem bad (P : Prop) (p : P) : Both (P -> P) P := by constructor <;> intro x"
    ));
}

#[test]
fn nested_controllers_and_grouped_chains_do_not_reenter_the_host_evaluator() {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap();
    let mut source = String::from("theorem same (n : Nat) : n = n := by\n");
    for depth in 0..200 {
        source.push_str(&format!("{}focus\n", "  ".repeat(depth + 1)));
    }
    source.push_str(&format!(
        "{}{}rfl{} <;> rfl\n",
        "  ".repeat(201),
        "(".repeat(1000),
        ")".repeat(1000)
    ));
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
fn invalid_unused_values_in_sequenced_proofs_reach_k1_rejection() {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap();
    for body in [
        "focus (have unused : String := 1; rfl)",
        "(have unused : String := 1; rfl) <;> rfl",
    ] {
        let source = format!("theorem bad : 0 = 0 := by {body}");
        let rejected = engine
            .check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits),
            )
            .unwrap_err();
        assert!(
            rejected.disposition().1,
            "expected kernel rejection: {rejected:?}"
        );
    }
}
