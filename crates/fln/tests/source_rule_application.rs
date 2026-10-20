//! Greedy rule application retains real obligations and ordinary dual admission.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Name, SourceCheckLimits};

fn engine() -> Engine {
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}
fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn check(base: &Engine, source: &str) -> Engine {
    base.check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits()),
    )
    .unwrap_or_else(|e| panic!("{source}\n{e:?}"))
    .into_complete()
    .unwrap()
    .engine
}
fn refuses(base: &Engine, source: &str) {
    let root = base.logical_root(&KVMap::new());
    assert!(
        base.check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits())
        )
        .is_err(),
        "{source}"
    );
    assert_eq!(base.logical_root(&KVMap::new()), root);
    assert!(!base.environment().contains(&Name::from_components(["bad"])));
}

#[test]
fn apply_assumption_performs_one_application_and_keeps_the_premises() {
    let base = engine();
    for source in [
        "theorem result (P Q : Prop) (hp : P) (f : P -> Q) : Q := by apply_assumption only [f]; exact hp",
        "theorem result (P Q R : Prop) (hp : P) (hq : Q) (f : P -> Q -> R) : R := by apply_assumption only [f]; exact hp; exact hq",
        "theorem result (P : Prop) (h : P) : P := by apply_assumption only [h]",
        "theorem result (P Q : Prop) (h : P) (f : P -> Q) : Q := by apply_assumption only [f h]",
    ] {
        check(&base, source);
    }
    refuses(
        &base,
        "theorem bad (P Q : Prop) (f : P -> Q) : Q := by apply_assumption only [f]",
    );
}

#[test]
fn repeated_rules_are_greedy_and_do_not_backtrack_to_a_later_lemma() {
    let base = engine();
    check(
        &base,
        "theorem result (P Q R : Prop) (hp : P) (hq : Q) (bad : Q -> R) (good : P -> R) : R := by apply_rules only [bad, good, hp]; guard_target = Q; exact hq",
    );
    refuses(
        &base,
        "theorem bad (P Q R : Prop) (hp : P) (bad : Q -> R) (good : P -> R) : R := by apply_rules only [bad, good, hp]",
    );
    check(
        &base,
        "theorem result (P Q R : Prop) (hp : P) (bad : Q -> R) (good : P -> R) : R := by solve_by_elim only [bad, good, hp]",
    );
}

#[test]
fn rule_iteration_limits_count_attempts_and_preserve_remaining_goals() {
    let base = engine();
    for source in [
        "theorem result (P Q R : Prop) (hp : P) (f : P -> Q) (g : Q -> R) : R := by apply_rules (maxDepth := 1) only [g, f, hp]; guard_target = Q; apply_assumption only [f]; exact hp",
        "theorem result (P Q R : Prop) (hp : P) (f : P -> Q) (g : Q -> R) : R := by apply_rules (maxDepth := 3) only [g, f, hp]",
        "theorem result (P : Prop) (hp : P) (loop : P -> P) : P := by apply_rules (maxDepth := 12) only [loop]; exact hp",
        "theorem result (P : Prop) (hp : P) : P := by first | apply_rules (maxDepth := 0) | exact hp",
    ] {
        check(&base, source);
    }
    refuses(
        &base,
        "theorem bad (P : Prop) (loop : P -> P) : P := by apply_rules (maxDepth := 8) only [loop]",
    );
}

#[test]
fn selected_polymorphic_rules_replay_and_close_dependent_parent_continuations() {
    let base = engine();
    for source in [
        "theorem result : (0 = 0) ∧ (true = true) := by apply_rules only [And.intro, Eq.refl]",
        "theorem result (A : Type) (x : A) : (x = x) ∧ (A = A) := by apply_rules only [And.intro, Eq.refl]",
        "theorem result (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by apply_rules (maxDepth := 1) only [And.intro]; exact hp; exact hq",
        "theorem result (P : Nat -> Prop) (h : P 3) (finish : (n : Nat) -> P n -> True) : True := by apply_rules only [finish, h]",
    ] {
        check(&base, source);
    }
}

#[test]
fn failed_rules_restore_state_and_respect_focus_and_selection() {
    let base = engine();
    for source in [
        "theorem result (P : Prop) (hp : P) : P := by first | apply_rules only [] | exact hp",
        "theorem result (P : Prop) (hp : P) : P := by\n  fail_if_success apply_assumption [-hp]\n  exact hp",
        "theorem result (P : Prop) (hp : P) : P := by apply_rules only [*]",
        "theorem result (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by\n  constructor\n  focus apply_rules only [hp]\n  exact hq",
        "theorem result (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by constructor <;> apply_assumption",
    ] {
        check(&base, source);
    }
    for source in [
        "theorem bad (P : Prop) (hp : P) : P := by apply_rules only []",
        "theorem bad (P : Prop) (hp : P) : P := by apply_rules [unknownLemma]",
        "theorem bad (P : Prop) (hp : P) : P := by apply_rules only [-hp]",
    ] {
        refuses(&base, source);
    }
}

#[test]
fn exfalso_fallback_builds_false_elimination_without_inventing_evidence() {
    let base = engine();
    for source in [
        "theorem result (P Q R : Prop) (hp : P) (hq : Q) (no : P -> Q -> False) : R := by apply_assumption only [no]; exact hp; exact hq",
        "theorem result (P Q R : Prop) (hp : P) (hq : Q) (no : P -> Q -> False) : R := by apply_rules only [no, hp, hq]",
        "theorem result (P Q : Prop) (hp : P) (no : P -> False) : Q := by\n  fail_if_success apply_rules -exfalso only [no, hp]\n  apply_rules only [no, hp]",
        "def result (no : False) : Nat := by apply_rules only [no]",
    ] {
        check(&base, source);
    }
    refuses(
        &base,
        "theorem bad (P Q R : Prop) (hp : P) (no : P -> Q -> False) : R := by apply_rules only [no, hp]",
    );
}

#[test]
fn symmetry_is_configurable_and_not_an_unconditional_rewrite() {
    let base = engine();
    for source in [
        "theorem result (x y : Nat) (h : x = y) : y = x := by apply_assumption",
        "theorem result (x y : Nat) (h : x = y) : y = x := by\n  fail_if_success apply_assumption -symm only [*]\n  symm\n  exact h",
        "theorem result (x y : Nat) (h : x = y) : y = x := by apply_rules (symm := true) only [*]",
    ] {
        check(&base, source);
    }
}

#[test]
fn ordinary_context_order_precedes_explicit_and_default_rules() {
    let base = engine();
    for source in [
        "theorem result (P Q : Prop) (hp : P) (first : P -> Q) (later : Q) : Q := by apply_assumption; guard_target = P; exact hp",
        "theorem result (P Q : Prop) (hp : P) (f : P -> Q) : Q := by apply_assumption [f hp]; guard_target = P; exact hp",
        "theorem result (P : Prop) (hp : P) (first : P -> True) : True := by apply_assumption; guard_target = P; exact hp",
        "theorem result (P : Prop) (hp : P) : P := by apply_assumption (maxDepth := 0) only [hp]",
    ] {
        check(&base, source);
    }
}

#[test]
fn malformed_or_unsupported_configuration_never_disappears_in_an_alternative() {
    let base = engine();
    for config in [
        "(unknown := true)",
        "(maxDepth := true)",
        "+maxDepth",
        "(symm := 1)",
        "(maxDepth := 1 + 2)",
        "(exfalso := unknown)",
        "(config := {})",
        "(transparency := .all)",
        "+backtracking",
        "(maxDepth := 18446744073709551616)",
    ] {
        refuses(
            &base,
            &format!(
                "theorem bad (P : Prop) (hp : P) : P := by first | apply_rules {config} only [hp] | exact hp"
            ),
        );
    }
    check(
        &base,
        "theorem result (P : Prop) (hp : P) : P := by apply_rules (maxDepth := (0x1)) (symm := (Bool.false)) +exfalso only [hp]",
    );
}

#[test]
fn a_later_dependent_sibling_can_assign_a_previously_retained_goal() {
    let base = engine();
    check(
        &base,
        "theorem result (P Q : Nat -> Prop) (p1 : P 1) (q1 : Q 1) (finish : (n : Nat) -> P n -> Q n -> True) : True := by apply_rules only [finish, p1, q1]",
    );
    check(
        &base,
        "theorem result (P Q : Prop) (hp : P) (hq : Q) : (P -> P) ∧ Q := by\n  constructor\n  focus intro h\n  apply_rules only [h]\n  exact hq",
    );
}
