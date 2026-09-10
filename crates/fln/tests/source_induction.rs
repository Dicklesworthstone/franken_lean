//! Source eliminations construct ordinary recursor proofs and scoped subgoals.
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
fn check(source: &str) -> fln::SourceFileCheck {
    engine()
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap()
}
#[test]
fn cases_specializes_the_goal_and_matches_constructor_names() {
    check(
        "theorem self (n : Nat) : n = n := by\n  cases n with\n  | succ k => rfl\n  | zero => rfl",
    );
    check("theorem self (b : Bool) : b = b := by cases b with | false => rfl | true => rfl");
}
#[test]
fn induction_proves_an_open_recursive_equation_using_its_hypothesis() {
    check(
        "def copy (n : Nat) : Nat := match n with | .zero => 0 | .succ k => Nat.succ (copy k)\ntheorem copy_ok (n : Nat) : copy n = n := by\n  induction n with\n  | zero => rfl\n  | succ k ih => simp only [copy, ih]",
    );
}
#[test]
fn both_recursive_tree_hypotheses_are_available_in_one_branch() {
    check(
        "inductive Tree where | leaf (n : Nat) | fork (left right : Tree)\ndef copy (t : Tree) : Tree := match t with | .leaf n => Tree.leaf n | .fork l r => Tree.fork (copy l) (copy r)\ntheorem copy_ok (t : Tree) : copy t = t := by\n  induction t with\n  | leaf n => rfl\n  | fork l r hl hr => simp only [copy, hl, hr]",
    );
}
#[test]
fn dependent_hypotheses_are_specialized_and_reintroduced() {
    check(
        "theorem dependent (n : Nat) (h : n = n) : n = n := by\n  cases n with\n  | zero => exact h\n  | succ k => exact h",
    );
}
#[test]
fn bare_cases_exposes_goals_to_the_following_sequence() {
    check("theorem self (b : Bool) : b = b := by\n  cases b\n  rfl\n  rfl");
}
#[test]
fn nested_branch_scripts_are_scoped() {
    check(
        "theorem self (a b : Bool) : a = a := by\n  cases a with\n  | false =>\n    cases b with\n    | false => rfl\n    | true => rfl\n  | true => rfl",
    );
}
#[test]
fn explicit_generalization_makes_hypotheses_functions_of_changed_arguments() {
    check(
        "def zeroAcc (n : Nat) (acc : Nat) : Nat := match n with | .zero => 0 | .succ k => zeroAcc k (acc + 1)\ntheorem zero_ok (n acc : Nat) : zeroAcc n acc = 0 := by\n  induction n generalizing acc with\n  | zero => rfl\n  | succ k ih => exact ih (acc + 1)",
    );
}
#[test]
fn dependent_hypotheses_are_generalized_in_the_induction_hypothesis() {
    check(
        "def copy (n : Nat) : Nat := match n with | .zero => 0 | .succ k => copy k\ntheorem copy_ok (n : Nat) (h : n = n) : copy n = 0 := by\n  induction n with\n  | zero => rfl\n  | succ k ih => exact ih rfl",
    );
}
#[test]
fn induction_is_not_secretly_available_to_cases_or_assumption() {
    let prefix = "def zero (n : Nat) : Nat := match n with | .zero => 0 | .succ k => zero k\n";
    check(&format!(
        "{prefix}theorem good (n : Nat) : zero n = 0 := by\n  induction n with\n  | zero => rfl\n  | succ k ih => exact ih"
    ));
    let base = engine();
    let source = format!(
        "{prefix}theorem bad (n : Nat) : zero n = 0 := by\n  cases n with\n  | zero => rfl\n  | succ k => assumption"
    );
    assert!(
        base.check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits())
        )
        .is_err()
    );
}
#[test]
fn empty_inductives_eliminate_without_fabricating_a_branch() {
    check("inductive Void where\ndef absurd (v : Void) : Nat := by cases v");
}
#[test]
fn dependent_record_case_analysis_returns_the_field_at_its_actual_type() {
    check(
        "structure Package where\n  carrier : Type\n  value : carrier\ndef unpack (p : Package) : p.carrier := by\n  cases p with\n  | mk carrier value => exact value\ndef p : Package := { carrier := Nat, value := 31 }\ntheorem unpack_ok : unpack p = 31 := by rfl",
    );
}
#[test]
fn introduced_locals_survive_case_splits_and_branch_shadowing() {
    check(
        "def self : Nat -> Nat -> Nat := by\n  intro n k\n  cases n with\n  | zero => exact k\n  | succ k => exact k\ntheorem zero_ok : self 0 8 = 8 := by rfl\ntheorem succ_ok : self 3 8 = 2 := by rfl",
    );
}
#[test]
fn parametric_payloads_and_constructor_qualified_names_are_preserved() {
    check(
        "inductive Maybe (A : Type) where | none | some (value : A)\ntheorem self {A : Type} (x : Maybe A) : x = x := by\n  cases x with\n  | Maybe.none => rfl\n  | Maybe.some a => rfl",
    );
}
#[test]
fn scoped_scripts_refuse_missing_extra_or_leaked_branch_work() {
    let bad = [
        "theorem t (n : Nat) : n = n := by cases n with | zero => rfl",
        "theorem t (n : Nat) : n = n := by cases n with | zero => rfl | zero => rfl",
        "theorem t (n : Nat) : n = n := by cases n with | zero extra => rfl | succ k => rfl",
        "theorem t (n : Nat) : n = n := by cases n with | zero => rfl | succ k ih => rfl",
        "theorem t (n : Nat) : n = n := by cases n with | zero => rfl | false => rfl",
        "theorem t (n : Nat) : n = n := by induction n with | zero => rfl | succ k k => rfl",
        "theorem t (n : Nat) : n = n := by\n  cases n with\n  | zero => rfl; rfl\n  | succ k => rfl",
        "def t (n : Nat) : Nat := by\n  cases n with\n  | zero => exact k\n  | succ k => exact k",
        "theorem t (n : Nat) : n = n := by\n  cases n with\n  | zero => simp only []\n  | succ k => exact n",
        "theorem t (n : Nat) : n = n := by induction n generalizing n with | zero => rfl | succ k ih => rfl",
        "theorem t (n : Nat) : n = n := by induction n generalizing missing with | zero => rfl | succ k ih => rfl",
    ];
    let base = engine();
    let before = base.environment().clone();
    for source in bad {
        assert!(
            base.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits())
            )
            .is_err(),
            "{source}"
        );
        assert_eq!(base.environment(), &before);
    }
}
#[test]
fn unsupported_parameterized_recursive_families_do_not_bypass_the_checker() {
    let base = engine();
    let before = base.logical_root(&KVMap::new());
    let error = base
        .check_source_files(
            &[b"inductive Chain (A : Type) where | nil | cons (head : A) (tail : Chain A)"],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .expect_err(
            "the independent checker does not yet admit this parameterized recursive shape",
        );
    assert_eq!(error.disposition(), ("inconclusive", false, 3));
    assert_eq!(base.logical_root(&KVMap::new()), before);
}
#[test]
fn transitive_data_dependencies_are_reintroduced_at_the_branch_type() {
    check(
        "def Carrier (n : Nat) : Type := match n with | .zero => Nat | .succ k => Bool\ndef keep (n : Nat) (x : Carrier n) (h : x = x) : Carrier n := by\n  cases n with\n  | zero => exact x\n  | succ k => exact x\ntheorem keep_ok : keep 0 9 rfl = 9 := by rfl",
    );
}
#[test]
fn local_let_dependencies_keep_their_values_without_becoming_parameters() {
    check(
        "def keep (n : Nat) : Nat := let saved := n; by\n  cases n with\n  | zero => exact saved\n  | succ k => exact saved\ntheorem keep_ok : keep 3 = 3 := by rfl",
    );
}
#[test]
fn false_proofs_and_invalid_unused_terms_still_reach_kernel_rejection() {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    for source in [
        "theorem false_proof (n : Nat) : 1 = 2 := by cases n with | zero => rfl | succ k => rfl",
        "def invalid (n : Nat) : Nat := by cases n with | zero => exact 0 | succ k => exact (1 : String)",
        "def invalid (n : Nat) : Nat := by cases n with | zero => exact 0 | succ k => exact ((fun unused => k) (1 : String))",
    ] {
        let error = base
            .check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits()),
            )
            .expect_err("every branch must check");
        assert_eq!(
            error.disposition(),
            ("kernel-rejection", true, 1),
            "{source}: {error:?}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
    }
}
#[test]
fn kernel_budget_exhaustion_is_not_an_induction_failure_or_success() {
    let base = engine();
    let mut low = SourceCheckLimits::new(limits());
    low.admission.kernel = low.admission.kernel.narrowed(0, 32);
    let result = base.check_source_files(&[b"theorem self (n : Nat) : n = n := by induction n with | zero => rfl | succ k ih => rfl"], &KVMap::new(), low);
    match result {
        Ok(fln::Outcome::Inconclusive(_)) => {}
        Err(error) => assert!(
            matches!(error.disposition(), ("resource" | "inconclusive", false, 3)),
            "{error:?}"
        ),
        other => panic!("expected a typed nonanswer: {other:?}"),
    }
}
#[test]
fn generalized_variables_must_not_invalidate_the_discriminant_type() {
    let source = b"inductive Maybe (A : Type) where | nil | some (head : A)\ntheorem self (A : Type) (xs : Maybe A) : xs = xs := by induction xs generalizing A with | nil => rfl | some head => rfl";
    assert!(
        engine()
            .check_source_files(&[source], &KVMap::new(), SourceCheckLimits::new(limits()))
            .is_err()
    );
}
