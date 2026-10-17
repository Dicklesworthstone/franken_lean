//! Contradiction preparation must leave ordinary, independently checked goals.
#![forbid(unsafe_code)]
use fln::{
    Budget, ConstantInfo, Engine, EngineAdmissionLimits, Expr, ExprNode, KVMap, Name,
    SourceCheckLimits,
};
use std::collections::HashSet;

fn n(name: &str) -> Name {
    Name::from_components(name.split('.'))
}

fn limits() -> SourceCheckLimits {
    SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(
        2 * 1024 * 1024,
    )))
}

fn seed() -> Engine {
    Engine::with_source_seed(limits().admission)
        .unwrap()
        .into_complete()
        .unwrap()
}

fn check(base: &Engine, source: &str) -> Engine {
    base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap()
        .engine
}

fn reject(base: &Engine, source: &str) {
    let root = base.logical_root(&KVMap::new());
    assert!(
        base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
            .is_err(),
        "unexpectedly accepted: {source}"
    );
    assert_eq!(base.logical_root(&KVMap::new()), root);
    assert!(!base.environment().contains(&n("bad")));
}

fn constructive_base() -> Engine {
    let base = seed();
    // The seed is not the full imported Init library. Supply a checked theorem
    // when its interface is absent; never add an axiom or an unchecked row.
    if base.environment().contains(&n("Decidable.byContradiction")) {
        return base;
    }
    check(
        &base,
        r#"
        theorem Decidable.byContradiction {p : Prop} [d : Decidable p]
            (h : (p -> False) -> False) : p := by
          cases d with
          | isFalse no => exact False.elim (h no)
          | isTrue yes => exact yes
        "#,
    )
}

fn with_classical_fixture(base: &Engine) -> Engine {
    let base = check(base, "inductive NativeContra : Prop where | intro");
    if base.environment().contains(&n("Classical.byContradiction")) {
        return base;
    }
    // A monomorphic, proved interface exercises fallback without introducing
    // classical axioms into the seed. There is deliberately no Decidable
    // registration for NativeContra. This is not an upstream-parity fixture.
    check(
        &base,
        r#"
        theorem Classical.byContradiction
            (h : (NativeContra -> False) -> False) : NativeContra := NativeContra.intro
        "#,
    )
}

fn theorem_uses(engine: &Engine, theorem: &str, constant: &str) -> bool {
    let Some(ConstantInfo::Thm(info)) = engine.environment().find(&n(theorem)) else {
        panic!("missing admitted theorem {theorem}");
    };
    uses(&info.value, &n(constant))
}

fn uses(expression: &Expr, name: &Name) -> bool {
    let mut pending = vec![expression];
    let mut seen = HashSet::new();
    while let Some(expression) = pending.pop() {
        if !seen.insert(expression.allocation_identity()) {
            continue;
        }
        match expression.node() {
            ExprNode::Const { name: found, .. } if found == name => return true,
            ExprNode::App { f, a } => pending.extend([f, a]),
            ExprNode::Lam {
                binder_type, body, ..
            }
            | ExprNode::ForallE {
                binder_type, body, ..
            } => pending.extend([binder_type, body]),
            ExprNode::LetE {
                type_, value, body, ..
            } => pending.extend([type_, value, body]),
            ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => pending.push(expr),
            _ => {}
        }
    }
    false
}

#[test]
fn false_targets_are_left_open_and_repeatable() {
    check(
        &seed(),
        r#"
        theorem unchanged (h : False) : False := by
          false_or_by_contra
          false_or_by_contra
          exact h
        "#,
    );
    reject(&seed(), "theorem bad : False := by false_or_by_contra");
}

#[test]
fn implications_negations_and_dependent_binders_keep_their_hypotheses() {
    let engine = check(
        &seed(),
        r#"
        theorem negative (p : Prop) : p -> ((p -> False) -> False) := by
          false_or_by_contra
          contradiction
        theorem dependent (P : Nat -> Prop) :
            (k : Nat) -> P k -> (P k -> False) -> False := by
          false_or_by_contra
          contradiction
        theorem hygienic (h : False) : True -> False := by
          false_or_by_contra
          exact h
        abbrev Negative (p : Prop) := p -> False
        theorem reducible (p : Prop) (h : Negative p) : Negative p := by
          false_or_by_contra
          contradiction
        "#,
    );
    for name in ["negative", "dependent", "hygienic", "reducible"] {
        assert!(!theorem_uses(&engine, name, "Classical.byContradiction"));
        assert!(!theorem_uses(&engine, name, "Decidable.byContradiction"));
    }
}

#[test]
fn data_and_polymorphic_goals_use_false_elimination_after_introductions() {
    check(
        &seed(),
        r#"
        universe u
        def impossible {A : Sort u} (h : False) : A := by
          false_or_by_contra
          exact h
        def impossibleFunction (h : False) : Nat -> Nat := by
          false_or_by_contra
          exact h
        theorem negativeData (h : False) : (Nat -> Nat) -> False := by
          false_or_by_contra
          exact h
        "#,
    );
}

#[test]
fn decidable_goals_use_constructive_contradiction() {
    let engine = check(
        &constructive_base(),
        r#"
        theorem constructive (p : Prop) [Decidable p]
            (h : (p -> False) -> False) : p := by
          false_or_by_contra
          have no : p -> False := by assumption
          exact h no
        "#,
    );
    assert!(theorem_uses(
        &engine,
        "constructive",
        "Decidable.byContradiction"
    ));
    assert!(!theorem_uses(
        &engine,
        "constructive",
        "Classical.byContradiction"
    ));
}

#[test]
fn constructive_application_precedes_an_available_classical_helper() {
    let base = with_classical_fixture(&constructive_base());
    let engine = check(
        &base,
        r#"
        theorem preferred [Decidable NativeContra] : NativeContra := by
          false_or_by_contra
          have no : NativeContra -> False := by assumption
          exact no NativeContra.intro
        "#,
    );
    assert!(theorem_uses(
        &engine,
        "preferred",
        "Decidable.byContradiction"
    ));
    assert!(!theorem_uses(
        &engine,
        "preferred",
        "Classical.byContradiction"
    ));
}

#[test]
fn failed_dictionary_synthesis_is_removed_before_classical_fallback() {
    let base = with_classical_fixture(&constructive_base());
    let root = base.logical_root(&KVMap::new());
    let engine = check(
        &base,
        r#"
        theorem fallback : NativeContra := by
          false_or_by_contra
          fail_if_success (have d : Decidable NativeContra := by infer_instance)
          have no : NativeContra -> False := by assumption
          exact no NativeContra.intro
        theorem following : NativeContra := NativeContra.intro
        "#,
    );
    assert!(theorem_uses(
        &engine,
        "fallback",
        "Classical.byContradiction"
    ));
    assert!(!theorem_uses(
        &engine,
        "fallback",
        "Decidable.byContradiction"
    ));
    assert_eq!(base.logical_root(&KVMap::new()), root);
}

#[test]
fn failed_alternatives_and_sibling_goals_keep_their_own_contexts() {
    let engine = check(
        &constructive_base(),
        r#"
        theorem recovered (p : Prop) [Decidable p] (h : p) : p := by
          first | (false_or_by_contra; fail) | exact h
        theorem siblings (p q : Prop) [Decidable p] [Decidable q]
            (hp : p) (hq : q) : p ∧ q := by
          constructor
          · false_or_by_contra
            contradiction
          · false_or_by_contra
            contradiction
        theorem restoredBinders (p : Prop) (h : p -> False) : p -> False := by
          first | (false_or_by_contra; fail) | exact h
        "#,
    );
    assert!(!theorem_uses(
        &engine,
        "recovered",
        "Decidable.byContradiction"
    ));
    assert!(!theorem_uses(
        &engine,
        "restoredBinders",
        "Decidable.byContradiction"
    ));
    assert!(theorem_uses(
        &engine,
        "siblings",
        "Decidable.byContradiction"
    ));
}

#[test]
fn missing_helpers_invalid_proofs_and_unfinished_goals_never_publish() {
    let base = constructive_base();
    for source in [
        "theorem bad (p : Prop) : p := by false_or_by_contra",
        "theorem bad (p : Prop) [Decidable p] : p := by false_or_by_contra",
        "def bad : Nat := by false_or_by_contra",
        "theorem bad : False := by false_or_by_contra; exact True.intro",
        "theorem bad (h : False) : False := by exact h; false_or_by_contra",
    ] {
        reject(&base, source);
    }
    // The unavailable classical fallback remains an ordinary recoverable
    // elaboration failure, rather than silently inventing an axiom.
    check(
        &base,
        "theorem recovered (p : Prop) (h : p) : p := by first | false_or_by_contra | exact h",
    );
}

#[test]
fn resource_stops_remain_nonanswers_inside_try() {
    let base = constructive_base();
    let root = base.logical_root(&KVMap::new());
    let source = b"theorem limited (p : Prop) [Decidable p] (h : p) : p := by try (false_or_by_contra; contradiction)";
    let mut low = limits();
    low.admission.kernel = low.admission.kernel.narrowed(0, 32);
    match base.check_source_files(&[source], &KVMap::new(), low) {
        Ok(fln::Outcome::Inconclusive(_)) => {}
        Err(error) => assert!(
            matches!(error.disposition(), ("resource" | "inconclusive", false, 3)),
            "{error:?}"
        ),
        other => panic!("resource exhaustion became an answer: {other:?}"),
    }
    assert_eq!(base.logical_root(&KVMap::new()), root);
    check(&base, std::str::from_utf8(source).unwrap());
}
