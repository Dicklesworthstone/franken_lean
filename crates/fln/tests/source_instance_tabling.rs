//! Real source -> instance synthesis -> kernel and independent checker admission.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};

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
fn checked(base: &Engine, source: &str) -> Engine {
    base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|error| panic!("source checking failed: {error:?}"))
        .into_complete()
        .unwrap()
        .engine
}

#[test]
fn repeated_ground_prerequisites_share_their_solved_dictionary() {
    let mut source = String::from("class D0 where\n  value : Nat\ninstance d0 : D0 := D0.mk 7\n");
    for depth in 1..=12 {
        let previous = depth - 1;
        source.push_str(&format!(
            "class D{depth} where\n  value : Nat\ninstance d{depth} [first : D{previous}] [second : D{previous}] : D{depth} := D{depth}.mk first.value\n"
        ));
    }
    let base = checked(&engine(), &source);
    checked(
        &base,
        "def result : D12 := inferInstance\ntheorem correct : result.value = 7 := by rfl",
    );
}

#[test]
fn a_cycle_dependent_fallback_is_not_reused_on_a_different_search_path() {
    checked(
        &engine(),
        r#"class A where
  value : Nat
class B where
  value : Nat
instance lowA : A := A.mk 2
instance lowB : B := B.mk 1
instance highA [b : B] : A := A.mk b.value
instance highB [a : A] : B := B.mk 3
class Pair where
  left : Nat
  right : Nat
instance pair [a : A] [b : B] : Pair := Pair.mk a.value b.value
def result : Pair := inferInstance
theorem leftValue : result.left = 1 := by rfl
theorem rightValue : result.right = 3 := by rfl"#,
    );
}

#[test]
fn solved_prerequisites_survive_branch_rollback_without_leaking_assignments() {
    let base = checked(
        &engine(),
        r#"class Leaf where
  value : Nat
instance leaf : Leaf := Leaf.mk 7
class Missing where
  value : Nat
class Root where
  value : Nat
instance fallback [l : Leaf] : Root := Root.mk l.value
instance failing [l : Leaf] [missing : Missing] : Root := Root.mk 99"#,
    );
    checked(
        &base,
        "def result : Root := inferInstance\ntheorem recovered : result.value = 7 := by rfl",
    );
    let before = base.logical_root(&KVMap::new());
    assert!(
        base.check_source_files(
            &[b"def rejected : Missing := inferInstance"],
            &KVMap::new(),
            limits(),
        )
        .is_err()
    );
    assert_eq!(before, base.logical_root(&KVMap::new()));
    checked(
        &base,
        "instance added : Missing := Missing.mk 4\ndef result : Root := inferInstance\ntheorem changed : result.value = 99 := by rfl",
    );
}

#[test]
fn repeated_impossible_prerequisites_do_not_starve_a_valid_fallback() {
    let mut source = String::from("class Dead0 where\n  value : Nat\n");
    for depth in 1..=12 {
        let previous = depth - 1;
        source.push_str(&format!(
            "class Dead{depth} where\n  value : Nat\ninstance left{depth} [d : Dead{previous}] : Dead{depth} := Dead{depth}.mk d.value\ninstance right{depth} [d : Dead{previous}] : Dead{depth} := Dead{depth}.mk d.value\n"
        ));
    }
    source.push_str("class Root where\n  value : Nat\ninstance fallback : Root := Root.mk 7\ninstance impossible [d : Dead12] : Root := Root.mk 99\n");
    let base = checked(&engine(), &source);
    checked(
        &base,
        "def result : Root := inferInstance\ntheorem recovered : result.value = 7 := by rfl",
    );
    let before = base.logical_root(&KVMap::new());
    let failure = base
        .check_source_files(
            &[b"def missing : Dead12 := inferInstance"],
            &KVMap::new(),
            limits(),
        )
        .unwrap_err();
    assert_eq!(failure.disposition(), ("elaboration", false, 1));
    assert_eq!(before, base.logical_root(&KVMap::new()));
    checked(
        &base,
        "instance supplied : Dead0 := Dead0.mk 1\ndef result : Root := inferInstance\ntheorem nowFound : result.value = 99 := by rfl",
    );
}

#[test]
fn a_cycle_dependent_failure_does_not_hide_a_solution_on_another_path() {
    checked(
        &engine(),
        r#"class A where
  value : Nat
class B where
  value : Nat
instance lowA : A := A.mk 2
instance highA [b : B] : A := A.mk b.value
instance highB [a : A] : B := B.mk 3
class Pair where
  left : Nat
  right : Nat
instance pair [a : A] [b : B] : Pair := Pair.mk a.value b.value
def result : Pair := inferInstance
theorem leftValue : result.left = 2 := by rfl
theorem rightValue : result.right = 3 := by rfl"#,
    );
}
