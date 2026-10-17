//! Explicit `unfold` reaches ordinary checked source admission.
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
        .unwrap_or_else(|e| {
            panic!(
                "{source}\
{e:?}"
            )
        })
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
fn unfold_expands_selected_safe_definitions_below_applications_and_binders() {
    let base = check(
        &engine(),
        r#"def wrapped (n : Nat) : Nat := n
def twice (n : Nat) : Nat := wrapped (wrapped n)"#,
    );
    check(
        &base,
        r#"theorem result : twice 7 = 7 := by
  unfold twice wrapped
  rfl"#,
    );
    check(
        &base,
        r#"theorem result (P : Nat -> Prop) (h : (n : Nat) -> P n) : (n : Nat) -> P (wrapped n) := by
  unfold wrapped
  exact h"#,
    );
}

#[test]
fn unfold_supports_named_goal_and_wildcard_locations_without_retagging_evidence() {
    let base = check(&engine(), "def wrapped (n : Nat) : Nat := n");
    check(
        &base,
        r#"theorem result (h : wrapped 1 = 1) : wrapped 2 = 2 := by
  unfold wrapped at h ⊢
  exact Eq.refl 2"#,
    );
    check(
        &base,
        r#"theorem result (h : wrapped 1 = 1) : wrapped 2 = 2 := by
  unfold wrapped at *
  rfl"#,
    );
}

#[test]
fn unfold_respects_local_let_shadowing_and_expands_the_selected_local_value() {
    let base = engine();
    check(
        &base,
        r#"theorem result : True := by
  let wrapped : Nat := 3
  have h : wrapped = 3 := by
    unfold wrapped
    rfl
  exact True.intro"#,
    );
}

#[test]
fn unfold_refuses_missing_nondefinitions_and_unsafe_definitions_atomically() {
    let base = check(&engine(), "def wrapped (n : Nat) : Nat := n");
    reject(
        &base,
        r#"theorem bad : True := by
  unfold wrapped
  exact True.intro"#,
    );
    reject(
        &base,
        r#"theorem bad (n : Nat) : n = n := by
  unfold n
  rfl"#,
    );
    let unsafe_base = check(&base, "unsafe def unsafeWrap (n : Nat) : Nat := n");
    reject(
        &unsafe_base,
        r#"theorem bad : True := by
  unfold unsafeWrap
  exact True.intro"#,
    );
}
