//! Configured proof search uses the source parser and ordinary checked admission.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Name, SourceCheckLimits};

fn limits() -> SourceCheckLimits {
    SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(
        2 * 1024 * 1024,
    )))
}
fn engine() -> Engine {
    Engine::with_source_seed(limits().admission)
        .unwrap()
        .into_complete()
        .unwrap()
}
fn check(base: &Engine, source: &str) -> Engine {
    base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|e| panic!("{source}\n{e:?}"))
        .into_complete()
        .unwrap()
        .engine
}
fn reject(base: &Engine, source: &str) {
    let root = base.logical_root(&KVMap::new());
    assert!(
        base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
            .is_err(),
        "{source}"
    );
    assert_eq!(base.logical_root(&KVMap::new()), root);
    assert!(!base.environment().contains(&Name::from_components(["bad"])));
}

fn chain(options: &str) -> String {
    let mut source = String::from("theorem result (P0 P1 P2 P3 P4 P5 P6 P7 P8 : Prop) (h : P0)");
    for i in 0..8 {
        source.push_str(&format!(" (f{i} : P{i} -> P{})", i + 1));
    }
    source.push_str(&format!(
        " : P8 := by solve_by_elim {options} only [h, f0, f1, f2, f3, f4, f5, f6, f7]"
    ));
    source
}

#[test]
fn configured_search_crosses_the_previous_hard_depth_six_boundary() {
    let base = engine();
    check(&base, &chain("(maxDepth := 10) -exfalso"));
    check(&base, &chain("(maxDepth := ((0x0a))) -exfalso"));
    reject(&base, &chain("-exfalso"));
    reject(&base, &chain("(maxDepth := 9) -exfalso"));
}

#[test]
fn depth_limits_count_direct_evidence_and_the_terminal_search_step() {
    let base = engine();
    // Backtrack.run tests its fuel before testing whether the goal list is empty.
    for depth in [0, 1] {
        reject(
            &base,
            &format!(
                "theorem bad (P : Prop) (h : P) : P := by solve_by_elim (maxDepth := {depth}) -exfalso only [h]"
            ),
        );
        reject(
            &base,
            &format!("theorem bad : 0 = 0 := by solve_by_elim (maxDepth := {depth}) -exfalso"),
        );
    }
    check(
        &base,
        "theorem result (P : Prop) (h : P) : P := by solve_by_elim (maxDepth := 2) only [h]",
    );
    check(
        &base,
        "theorem result : 0 = 0 := by solve_by_elim (maxDepth := 2)",
    );
    check(
        &base,
        "theorem result (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by\n  constructor\n  solve_by_elim* (maxDepth := 2) only [hp, hq]",
    );
}

#[test]
fn introductions_and_constructor_discharge_can_be_disabled_independently() {
    let base = engine();
    reject(
        &base,
        "theorem bad (P : Prop) : P -> P := by solve_by_elim -intro -exfalso",
    );
    check(
        &base,
        "theorem result (P : Prop) : P -> P := by solve_by_elim +intro -constructor (maxDepth := 3)",
    );
    reject(
        &base,
        "theorem bad (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by solve_by_elim -constructor -exfalso",
    );
    check(
        &base,
        "theorem result (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by solve_by_elim -constructor only [And.intro, hp, hq]",
    );
    check(
        &base,
        "theorem result : True := by solve_by_elim -intro +constructor only []",
    );
    reject(
        &base,
        "theorem bad : True := by solve_by_elim -intro -constructor -exfalso only []",
    );
    // True.intro is also a default lemma; turning off a discharger must not erase it.
    check(
        &base,
        "theorem result : True := by solve_by_elim -intro -constructor",
    );
}

#[test]
fn symmetry_and_whole_search_exfalso_obey_the_selected_options() {
    let base = engine();
    let equality =
        "theorem result (x y : Nat) (h : x = y) : y = x := by solve_by_elim OPTIONS only [h]";
    check(&base, &equality.replace("OPTIONS", "+symm"));
    reject(&base, &equality.replace("OPTIONS", "-symm -exfalso"));
    let false_goal = "theorem result (P Q : Prop) (h : P) (no : P -> False) : Q := by solve_by_elim OPTIONS only [h, no]";
    check(&base, &false_goal.replace("OPTIONS", "+exfalso"));
    reject(&base, &false_goal.replace("OPTIONS", "-exfalso"));
    check(
        &base,
        "theorem result (P Q : Prop) (h : P) (no : P -> False) : Q := by first | solve_by_elim -exfalso only [h, no] | solve_by_elim +exfalso only [h, no]",
    );
}

#[test]
fn configured_joint_search_keeps_dependent_witnesses_and_focus_boundaries() {
    let base = engine();
    let dependent = "theorem result (P Q : Nat -> Prop) (p1 : P 1) (q1 : Q 1) (finish : (n : Nat) -> P n -> Q n -> True) : True := by\n  apply finish\n  solve_by_elim* (maxDepth := DEPTH) -exfalso -constructor -intro only [p1, q1]";
    reject(&base, &dependent.replace("DEPTH", "2"));
    check(&base, &dependent.replace("DEPTH", "3"));
    check(
        &base,
        "theorem result (P Q : Nat -> Prop) (p1 : P 1) (q1 : Q 1) (p0 : P 0) (finish : (n : Nat) -> P n -> Q n -> True) : True := by\n  apply finish\n  solve_by_elim* (maxDepth := 10) -constructor -intro only [p0, p1, q1]",
    );
    check(
        &base,
        "theorem result (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by\n  constructor\n  focus solve_by_elim* (maxDepth := 2) only [hp]\n  exact hq",
    );
    check(
        &base,
        "theorem result (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by\n  constructor\n  first | solve_by_elim* (maxDepth := 2) only [hp] | solve_by_elim* (maxDepth := 2) only [hp, hq]",
    );
    reject(
        &base,
        "theorem bad (P Q : Prop) (hp : P) (no : P -> False) : Q ∧ Q := by\n  constructor\n  solve_by_elim* (maxDepth := 12) +exfalso",
    );
}

#[test]
fn configuration_is_local_to_the_invocation_and_literal_boolean_syntax() {
    let base = engine();
    check(
        &base,
        "theorem first : True := by solve_by_elim -constructor only [True.intro]\ntheorem second (P : Prop) : P -> P := by solve_by_elim\ntheorem third (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by solve_by_elim",
    );
    check(
        &base,
        "theorem result (P : Prop) (false : P) : P := by solve_by_elim (symm := Bool.false) (intro := (true)) (constructor := false) only [false]",
    );
}

#[test]
fn unsupported_computed_and_oversized_configuration_cannot_hide_behind_evidence() {
    let base = engine();
    for config in [
        "(config := {})",
        "(maxDepth := n)",
        "(maxDepth := 2 + 2)",
        "+maxDepth",
        "(symm := f)",
        "(intro := Bool.not false)",
        "(constructor := 1)",
        "+suggestions",
        "(transparency := .all)",
        "-backtracking",
        "(maxDepth := 18446744073709551616)",
    ] {
        reject(
            &base,
            &format!(
                "theorem bad (P : Prop) (h : P) : P := by first | solve_by_elim {config} only [h] | exact h"
            ),
        );
    }
    check(
        &base,
        "theorem result (P : Prop) (h : P) : P := by solve_by_elim (maxDepth := 2) only [h]",
    );
}
