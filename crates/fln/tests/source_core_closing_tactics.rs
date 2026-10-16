//! Small core tactics must create ordinary checked proof terms.
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

#[test]
fn exfalso_applies_the_admitted_false_eliminator_and_leaves_real_evidence_goals() {
    let base = engine();
    check(
        &base,
        "theorem result (P : Prop) (h : False) : P := by exfalso; exact h",
    );
    check(
        &base,
        r#"theorem result (P Q : Prop) (h : False) : P ∧ Q := by
  constructor <;> exfalso <;> exact h"#,
    );
    check(
        &base,
        "theorem result (h : False) : False := by exfalso; exact h",
    );
}

#[test]
fn infer_instance_closes_prop_and_data_class_goals_with_registered_dictionaries() {
    let base = check(
        &engine(),
        "class Ready : Prop where\n  ok : True\ninstance ready : Ready := ⟨True.intro⟩",
    );
    check(&base, "theorem result : Ready := by infer_instance");
    check(&base, "def result : Inhabited Nat := by infer_instance");
}

#[test]
fn missing_instance_is_recoverable_but_cannot_publish_a_bad_theorem() {
    let base = check(&engine(), "class Missing : Prop where\n  ok : True");
    reject(&base, "theorem bad : Missing := by infer_instance");
    check(
        &base,
        "theorem recovered (h : Missing) : Missing := by first | infer_instance | exact h",
    );
}

#[test]
fn unsafe_selected_instances_cannot_escape_into_safe_theorems() {
    let base = check(
        &engine(),
        "unsafe instance (priority := 2000) unsafePick : Inhabited Nat := ⟨42⟩",
    );
    reject(&base, "def bad : Inhabited Nat := by infer_instance");
}
