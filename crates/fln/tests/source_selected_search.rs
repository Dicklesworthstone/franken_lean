//! Selected proof search through the source parser and ordinary dual-checker council.
#![forbid(unsafe_code)]

use fln::{Engine, EngineAdmissionLimits};
use fln_core::{expr::ExprNode, name::Name, options::KVMap};
use fln_env::constants::ConstantInfo;
use fln_kernel::verdict::Budget;

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}

fn engine() -> Engine {
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}

fn admit(base: &Engine, source: &str) -> Engine {
    base.admit_source_declaration(source.as_bytes(), &KVMap::new(), limits())
        .unwrap_or_else(|problem| panic!("{source}\n{problem:?}"))
        .into_complete()
        .expect("the ordinary council must complete")
        .engine
}

fn rejected(base: &Engine, source: &str) {
    assert!(
        base.admit_source_declaration(source.as_bytes(), &KVMap::new(), limits())
            .is_err(),
        "unexpectedly admitted {source}"
    );
    assert!(
        base.environment()
            .find(&Name::from_components(["bad"]))
            .is_none()
    );
}

#[test]
fn selected_local_lemmas_and_partially_applied_terms_prove_real_goals() {
    let base = engine();
    for source in [
        "theorem selected (P Q : Prop) (h : P) (f : P -> Q) : Q := by solve_by_elim only [f, h]",
        "theorem selected (P Q : Prop) (h : P) (f : P -> Q) : Q := by solve_by_elim [f h]",
        "theorem selected (P : Prop) (h : P) : P := by solve_by_elim only [*]",
        "theorem selected (P : Prop) (h : P) : P := by solve_by_elim only [h, h]",
    ] {
        admit(&base, source);
    }
}

#[test]
fn named_global_lemma_is_retained_in_the_checked_proof() {
    let base = admit(&engine(), "theorem relay (P : Prop) (h : P) : P := h");
    let result = admit(
        &base,
        "theorem selected (P : Prop) (h : P) : P := by solve_by_elim only [relay P h]",
    );
    let ConstantInfo::Thm(theorem) = result
        .environment()
        .find(&Name::from_components(["selected"]))
        .unwrap()
    else {
        panic!("search must publish a theorem, never an axiom");
    };
    assert!(!theorem.value.has_fvar());
    assert!(!theorem.value.has_expr_mvar());
    assert!(!theorem.value.has_level_mvar());
    assert!(!theorem.value.has_loose_bvars());
    let mut pending = vec![&theorem.value];
    let mut found = false;
    while let Some(expr) = pending.pop() {
        match expr.node() {
            ExprNode::Const { name, .. } if name == &Name::from_components(["relay"]) => {
                found = true
            }
            ExprNode::App { f, a } => pending.extend([f, a]),
            ExprNode::Lam {
                binder_type, body, ..
            }
            | ExprNode::ForallE {
                binder_type, body, ..
            } => pending.extend([binder_type, body]),
            _ => {}
        }
    }
    assert!(
        found,
        "selected global evidence must remain a real proof dependency"
    );
}

#[test]
fn a_polymorphic_selected_lemma_is_reelaborated_for_each_application() {
    let base = engine();
    for source in [
        "theorem selected : (0 = 0) ∧ (true = true) := by solve_by_elim only [And.intro, Eq.refl]",
        "theorem selected (A : Type) (x : A) : (x = x) ∧ (A = A) := by solve_by_elim only [And.intro, Eq.refl]",
    ] {
        admit(&base, source);
    }
}

#[test]
fn erased_hypotheses_are_excluded_but_can_be_explicitly_readded() {
    let base = engine();
    for source in [
        "theorem selected (P : Prop) (h : P) : P := by\n  fail_if_success solve_by_elim [-h]\n  exact h",
        "theorem selected (P : Prop) (h : P) : P := by\n  fail_if_success solve_by_elim only [*, -h]\n  exact h",
        "theorem selected (P : Prop) (h : P) : P := by solve_by_elim [-h, h]",
        "theorem selected (P : Prop) (h : P) : P := by solve_by_elim only [*, -h, h]",
    ] {
        admit(&base, source);
    }
}

#[test]
fn only_does_not_silently_use_an_unselected_local() {
    let base = engine();
    rejected(
        &base,
        "theorem bad (P Q : Prop) (h : P) (f : P -> Q) : Q := by solve_by_elim only [f]",
    );
    admit(
        &base,
        "theorem selected (P Q : Prop) (h : P) (f : P -> Q) : Q := by first | solve_by_elim only [f] | exact f h",
    );
}

#[test]
fn an_unused_invalid_argument_is_not_hidden_by_a_matching_local() {
    let base = engine();
    for source in [
        "theorem bad (P : Prop) (h : P) : P := by solve_by_elim [unknownLemma]",
        "theorem bad (P : Prop) (h : P) : P := by solve_by_elim [-unknownLemma]",
        "theorem bad (P : Prop) (h : P) : P := by solve_by_elim [*]",
        "theorem bad (P : Prop) (h : P) : P := by solve_by_elim only [-h]",
    ] {
        rejected(&base, source);
    }
}

#[test]
fn selected_search_backtracks_after_a_later_premise_fails() {
    let base = engine();
    admit(
        &base,
        "theorem selected (P Q R : Prop) (h : P) (good : P -> R) (bad : Q -> R) : R := by solve_by_elim only [bad, good, h]",
    );
    admit(
        &base,
        "theorem selected (x y : Nat) (P Q : Prop) (h : x = y) (good : y = x -> P) (bad : Q -> P) : P := by solve_by_elim only [bad, good, h]",
    );
}

#[test]
fn selected_search_never_turns_a_cycle_or_false_equality_into_evidence() {
    let base = engine();
    for source in [
        "theorem bad (P : Prop) (cycle : P -> P) : P := by solve_by_elim only [cycle]",
        "theorem bad : 1 = 2 := by solve_by_elim only [Eq.refl]",
        "theorem bad (P : Prop) : P := by solve_by_elim only [And.intro]",
    ] {
        rejected(&base, source);
    }
}

#[test]
fn joint_search_solves_every_visible_goal_with_fresh_local_contexts() {
    let base = engine();
    for source in [
        "theorem selected (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by\n  constructor\n  solve_by_elim*",
        "theorem selected : (0 = 0) ∧ (true = true) := by\n  constructor\n  solve_by_elim* only [Eq.refl]",
        "theorem selected (P : Prop) : (P -> P) ∧ (P -> P) := by\n  constructor\n  all_goals intro h\n  solve_by_elim* only [h]",
    ] {
        admit(&base, source);
    }
}

#[test]
fn joint_search_backtracks_across_dependent_sibling_goals() {
    let base = engine();
    // The first matching P witness is 0, but only 1 has a Q witness. Search
    // must revisit its earlier P choice when the later Q obligation fails.
    let source = "theorem selected (P Q : Nat -> Prop) (p1 : P 1) (q1 : Q 1) (p0 : P 0) (finish : (n : Nat) -> P n -> Q n -> True) : True := by\n  apply finish\n  solve_by_elim* only [p0, p1, q1]";
    admit(&base, source);
    rejected(
        &base,
        &source
            .replace("theorem selected", "theorem bad")
            .replace("solve_by_elim*", "all_goals solve_by_elim"),
    );
}

#[test]
fn failed_joint_search_restores_all_goals_before_an_alternative() {
    let base = engine();
    admit(
        &base,
        "theorem selected (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by\n  constructor\n  first | solve_by_elim* only [hp] | solve_by_elim* only [hp, hq]",
    );
    rejected(
        &base,
        "theorem bad (P Q : Prop) (hp : P) : P ∧ Q := by\n  constructor\n  solve_by_elim* only [hp]",
    );
}

#[test]
fn joint_search_respects_focus_and_option_boundaries() {
    let base = engine();
    for source in [
        "theorem selected (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by\n  constructor\n  · solve_by_elim*\n  · exact hq",
        "theorem selected (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by\n  constructor\n  focus solve_by_elim*\n  exact hq",
        "theorem selected (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by\n  constructor\n  set_option maxHeartbeats 200000 in solve_by_elim*",
        "theorem selected (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by\n  constructor <;> solve_by_elim*",
    ] {
        admit(&base, source);
    }
}

#[test]
fn joint_search_rejects_cross_goal_erasure_and_does_not_drop_siblings() {
    let base = engine();
    for source in [
        "theorem bad (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by\n  constructor\n  solve_by_elim* [-hp]",
        "theorem bad (P Q : Prop) (hp : P) : P ∧ Q := by\n  constructor\n  focus solve_by_elim*",
        "theorem bad (P Q : Prop) (hp : P) : P ∧ Q := by\n  constructor\n  solve_by_elim* only [hp]",
    ] {
        rejected(&base, source);
    }
    admit(
        &base,
        "theorem selected (P : Prop) (hp : P) : P := by solve_by_elim* [-hp, hp]",
    );
}

#[test]
fn joint_lemma_names_are_validated_in_each_goals_own_context() {
    let base = engine();
    rejected(
        &base,
        "theorem bad (P Q : Prop) (hq : Q) : (P -> P) ∧ Q := by\n  constructor\n  focus intro h\n  solve_by_elim* only [h, hq]",
    );
    admit(
        &base,
        "theorem selected (P Q : Prop) (hq : Q) : (P -> P) ∧ Q := by\n  constructor\n  focus intro h\n  solve_by_elim*",
    );
}
