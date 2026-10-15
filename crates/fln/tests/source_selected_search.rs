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
