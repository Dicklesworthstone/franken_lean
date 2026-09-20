//! Dependent output dictionaries are inferred, then admitted by both checkers.
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
        .unwrap_or_else(|error| panic!("source checking failed: {error:?}\n{source}"))
        .into_complete()
        .unwrap()
        .engine
}
fn dependent_tree(depth: usize) -> String {
    let mut source = String::from(
        "class D0 (A : outParam Type) (a : outParam A) where\n  value : Nat\ninstance d0 : D0 Nat 7 := D0.mk 7\n",
    );
    for level in 1..=depth {
        let previous = level - 1;
        source.push_str(&format!(
            "class D{level} (A : outParam Type) (a : outParam A) where\n  value : Nat\ninstance d{level} {{A B : Type}} {{a : A}} {{b : B}} [left : D{previous} A a] [right : D{previous} B b] : D{level} A a := D{level}.mk left.value\n"
        ));
    }
    source.push_str(&format!(
        "class Answer where\n  value : Nat\ninstance answer {{A : Type}} {{a : A}} [dict : D{depth} A a] : Answer := Answer.mk dict.value\n"
    ));
    source
}
#[test]
fn dependent_output_control() {
    let base = checked(&engine(), &dependent_tree(1));
    checked(
        &base,
        "def result : Answer := inferInstance\ntheorem resultValue : result.value = 7 := by rfl",
    );
}
#[test]
fn repeated_dependent_outputs_share_their_type_and_value_dictionary() {
    let base = checked(&engine(), &dependent_tree(12));
    checked(
        &base,
        "def result : Answer := inferInstance\ntheorem resultValue : result.value = 7 := by rfl",
    );
}

#[test]
fn dependent_cached_answers_resume_after_later_prerequisites_fail() {
    checked(
        &engine(),
        r#"class D (A : outParam Type) (a : outParam A) where
  value : Nat
instance low : D Nat 7 := D.mk 7
instance high : D Bool true := D.mk 99
class Accept (A : Type) (a : A) where
  value : Nat
instance accept : Accept Nat 7 := Accept.mk 7
class Root where
  first : Nat
  second : Nat
instance root {A B : Type} {a : A} {b : B} [left : D A a] [right : D B b] [ok : Accept B b] : Root := Root.mk left.value right.value
def result : Root := inferInstance
theorem firstValue : result.first = 99 := by rfl
theorem secondValue : result.second = 7 := by rfl"#,
    );
}

#[test]
fn fixed_dependent_outputs_do_not_filter_higher_priority_instances() {
    let base = checked(
        &engine(),
        r#"class D (A : outParam Type) (a : outParam A) where
  value : Nat
instance low : D Nat 7 := D.mk 7
instance high : D Bool true := D.mk 99
class Root where
  value : Nat
instance root {A : Type} {a : A} [warm : D A a] [fixed : D Nat 7] : Root := Root.mk fixed.value"#,
    );
    let before = base.logical_root(&KVMap::new());
    assert!(
        base.check_source_files(
            &[b"def rejected : Root := inferInstance"],
            &KVMap::new(),
            limits()
        )
        .is_err()
    );
    assert_eq!(base.logical_root(&KVMap::new()), before);
    checked(
        &base,
        r#"instance newest : D Nat 7 := D.mk 42
def result : Root := inferInstance
theorem recovered : result.value = 42 := by rfl"#,
    );
}

#[test]
fn repeated_impossible_dependent_outputs_reach_fallback_and_recover() {
    let mut source =
        String::from("class D0 (A : outParam Type) (a : outParam A) where\n  value : Nat\n");
    for level in 1..=12 {
        let previous = level - 1;
        source.push_str(&format!(
            "class D{level} (A : outParam Type) (a : outParam A) where\n  value : Nat\ninstance a{level} {{A : Type}} {{a : A}} [prev : D{previous} A a] : D{level} A a := D{level}.mk prev.value\ninstance b{level} {{A : Type}} {{a : A}} [prev : D{previous} A a] : D{level} A a := D{level}.mk prev.value\n"
        ));
    }
    source.push_str("class Answer where\n  value : Nat\ninstance fallback : Answer := Answer.mk 4\ninstance preferred {A : Type} {a : A} [dict : D12 A a] : Answer := Answer.mk dict.value\n");
    let base = checked(&engine(), &source);
    checked(
        &base,
        "def result : Answer := inferInstance\ntheorem fallbackValue : result.value = 4 := by rfl",
    );
    checked(
        &base,
        "instance leaf : D0 Nat 7 := D0.mk 7\ndef result : Answer := inferInstance\ntheorem preferredValue : result.value = 7 := by rfl",
    );
}
