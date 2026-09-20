//! Polymorphic instance queries keep inferred universes and proof authority.
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
        .unwrap_or_else(|error| {
            panic!(
                "source checking failed: {:?}\n{source}",
                error.disposition()
            )
        })
        .into_complete()
        .unwrap()
        .engine
}
fn polymorphic_tree(depth: usize) -> String {
    let mut source = String::from(
        "class U0.{u} (A : outParam (Type u)) where\n  value : Nat\ninstance u0 : U0 Nat := U0.mk 7\n",
    );
    for level in 1..=depth {
        let previous = level - 1;
        source.push_str(&format!("class U{level}.{{u}} (A : outParam (Type u)) where\n  value : Nat\ninstance u{level}.{{u,v}} {{A : Type u}} {{B : Type v}} [left : U{previous} A] [right : U{previous} B] : U{level} Nat := U{level}.mk left.value\n"));
    }
    source.push_str(&format!("class Answer where\n  value : Nat\ninstance answer.{{u}} {{A : Type u}} [dict : U{depth} A] : Answer := Answer.mk dict.value\n"));
    source
}
#[test]
fn polymorphic_output_control() {
    let base = checked(&engine(), &polymorphic_tree(1));
    checked(
        &base,
        "def result : Answer := inferInstance\ntheorem correct : result.value = 7 := by rfl",
    );
}
#[test]
fn repeated_polymorphic_prerequisites_infer_their_own_universes() {
    let base = checked(&engine(), &polymorphic_tree(9));
    checked(
        &base,
        "def result : Answer := inferInstance\ntheorem correct : result.value = 7 := by rfl",
    );
}

#[test]
fn cached_polymorphic_answers_backtrack_across_universe_assignments() {
    checked(
        &engine(),
        r#"class Carrier.{u} (A : outParam (Type u)) where
  value : Nat
instance low : Carrier Nat := Carrier.mk 7
instance high : Carrier Type := Carrier.mk 99
class Allowed.{u} (A : Type u) where
  value : Nat
instance allowed : Allowed Nat := Allowed.mk 7
class Root where
  first : Nat
  second : Nat
instance root.{u,v} {A : Type u} {B : Type v} [first : Carrier A] [second : Carrier B] [valid : Allowed B] : Root := Root.mk first.value second.value
def result : Root := inferInstance
theorem firstValue : result.first = 99 := by rfl
theorem secondValue : result.second = 7 := by rfl"#,
    );
}

#[test]
fn polymorphic_missing_queries_do_not_poison_future_registry_extensions() {
    let base = checked(
        &engine(),
        r#"class Carrier.{u} (A : outParam (Type u)) where
  value : Nat
class Root where
  value : Nat
instance root.{u,v} {A : Type u} {B : Type v} [first : Carrier A] [second : Carrier B] : Root := Root.mk second.value"#,
    );
    let before = base.logical_root(&KVMap::new());
    assert!(
        base.check_source_files(
            &[b"def missing : Root := inferInstance"],
            &KVMap::new(),
            limits()
        )
        .is_err()
    );
    assert_eq!(base.logical_root(&KVMap::new()), before);
    checked(
        &base,
        r#"instance added : Carrier Type := Carrier.mk 12
def result : Root := inferInstance
theorem recovered : result.value = 12 := by rfl"#,
    );
}

#[test]
fn known_universe_and_output_types_remain_distinct_from_open_variants() {
    checked(
        &engine(),
        r#"class Carrier.{u} (A : outParam (Type u)) where
  value : Nat
instance low : Carrier Nat := Carrier.mk 7
instance high : Carrier Type := Carrier.mk 99
class Root where
  openValue : Nat
  fixedValue : Nat
instance root.{u} {A : Type u} [first : Carrier A] [fixed : Carrier Nat] : Root := Root.mk first.value fixed.value
def result : Root := inferInstance
theorem openValue : result.openValue = 99 := by rfl
theorem fixedValue : result.fixedValue = 7 := by rfl"#,
    );
}
