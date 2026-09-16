//! Source-level coercions are ordinary terms checked by both engines.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};
fn limits() -> SourceCheckLimits {
    SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(
        2 * 1024 * 1024,
    )))
}
fn seed() -> Engine {
    Engine::with_coercion_seed(limits().admission)
        .unwrap()
        .into_complete()
        .unwrap()
}
fn checked(base: &Engine, source: &str) -> Engine {
    base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|e| panic!("{source}\n{e:?}"))
        .into_complete()
        .unwrap()
        .engine
}
#[test]
fn staged_coercion_library_is_admitted_by_both_checkers() {
    checked(
        &seed(),
        "structure Box where\n  value : Nat\ninstance boxToNat : Coe Box Nat := Coe.mk (fun x => x.value)\ndef unpack (x : Box) : Nat := Coe.coe x",
    );
}

#[test]
fn direct_coercions_check_arguments_results_and_let_annotations() {
    checked(
        &seed(),
        r#"structure Box where
  value : Nat
instance boxToNat : Coe Box Nat := Coe.mk (fun b => b.value)
def value : Box := Box.mk 17
def asResult : Nat := value
def take (n : Nat) : Nat := n + 2
def asArgument := take value
def inLet : Nat := let n : Nat := value; n
theorem result_ok : asResult = 17 := by rfl
theorem argument_ok : asArgument = 19 := by rfl
theorem let_ok : inLet = 17 := by rfl"#,
    );
}

#[test]
fn function_coercions_apply_real_record_fields() {
    checked(
        &seed(),
        r#"structure FnBox where
  run : Nat -> Nat
instance callable : CoeFun FnBox (fun f => Nat -> Nat) := CoeFun.mk (fun f => f.run)
def boxed : FnBox := FnBox.mk (fun n => n + 3)
def applied := boxed 9
theorem works : applied = 12 := by rfl"#,
    );
}

#[test]
fn sort_coercions_elaborate_bundled_type_annotations() {
    checked(
        &seed(),
        r#"structure Bundle where
  carrier : Type
instance bundled : CoeSort Bundle Type := CoeSort.mk (fun b => b.carrier)
def numbers : Bundle := Bundle.mk Nat
def number : numbers := 7
theorem works : number = 7 := by rfl"#,
    );
}

#[test]
fn type_coercions_compose_through_intermediate_types() {
    checked(
        &seed(),
        r#"structure A where
  value : Nat
structure B where
  value : Nat
instance ab : Coe A B := Coe.mk (fun a => B.mk (a.value + 1))
instance bn : Coe B Nat := Coe.mk (fun b => b.value + 2)
def converted : Nat := A.mk 7
theorem works : converted = 10 := by rfl"#,
    );
}

#[test]
fn dependent_coercions_match_the_value_not_just_its_type() {
    let base = checked(
        &seed(),
        r#"instance oneBool : CoeDep Nat 1 Bool := CoeDep.mk true
def one : Nat := 1
def answer : Bool := (1 : Nat)
theorem works : answer = true := by rfl"#,
    );
    assert!(
        base.check_source_files(&[b"def other : Bool := (2 : Nat)"], &KVMap::new(), limits())
            .is_err()
    );
}

#[test]
fn coercion_search_backtracks_a_successful_edge_when_the_rest_of_the_path_fails() {
    checked(
        &seed(),
        r#"structure A where
  value : Nat
structure B where
  value : Nat
structure C where
  value : Nat
instance ac : Coe A C := Coe.mk (fun a => C.mk a.value)
instance cn : Coe C Nat := Coe.mk (fun c => c.value + 2)
instance (priority := 2000) deadEnd : Coe B Nat := Coe.mk (fun b => b.value + 99)
def converted : Nat := A.mk 7
theorem works : converted = 9 := by rfl"#,
    );
}

#[test]
fn definitional_equality_precedes_nonidentity_conversion() {
    checked(
        &seed(),
        r#"structure Indexed (n : Nat) where
  value : Nat
instance shouldNotRun : Coe (Indexed (2 + 3)) (Indexed 5) := Coe.mk (fun a => Indexed.mk 999)
def original : Indexed (2 + 3) := Indexed.mk 17
def unchanged : Indexed 5 := original
theorem works : unchanged.value = 17 := by rfl"#,
    );
}

#[test]
fn callable_records_coerce_to_function_arguments() {
    checked(
        &seed(),
        r#"structure FnBox where
  run : Nat -> Nat
instance callable : CoeFun FnBox (fun f => Nat -> Nat) := CoeFun.mk (fun f => f.run)
def use (f : Nat -> Nat) : Nat := f 9
def boxed : FnBox := FnBox.mk (fun n => n + 3)
def applied := use boxed
theorem works : applied = 12 := by rfl"#,
    );
}
