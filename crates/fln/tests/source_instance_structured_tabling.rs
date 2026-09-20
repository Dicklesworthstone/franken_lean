//! Structured output inference remains checked and resumable across table hits.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};

fn limits() -> SourceCheckLimits {
    SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(
        2 * 1024 * 1024,
    )))
}
fn checked(base: &Engine, source: &str) -> Engine {
    base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|error| panic!("source checking failed: {error:?}\n{source}"))
        .into_complete()
        .unwrap()
        .engine
}
fn seed() -> Engine {
    Engine::with_source_seed(limits().admission)
        .unwrap()
        .into_complete()
        .unwrap()
}

fn repeated(shape: &str) {
    let mut source = String::from("structure Box (A : Type) where\n  value : A\n");
    let concrete = shape.replace("?", "Nat");
    let left = shape.replace("?", "A");
    let right = shape.replace("?", "B");
    source.push_str(&format!("class C0 (A : outParam Type) where\n  value : Nat\ninstance c0 : C0 ({concrete}) := C0.mk 7\n"));
    for depth in 1..=12 {
        let previous = depth - 1;
        source.push_str(&format!("class C{depth} (A : outParam Type) where\n  value : Nat\ninstance c{depth} {{A B : Type}} [first : C{previous} ({left})] [second : C{previous} ({right})] : C{depth} ({concrete}) := C{depth}.mk first.value\n"));
    }
    let base = checked(&seed(), &source);
    checked(
        &base,
        &format!(
            "def result : C12 ({concrete}) := inferInstance\ntheorem correct : result.value = 7 := by rfl"
        ),
    );
}

#[test]
fn repeated_constructor_output_patterns_infer_their_nested_holes() {
    repeated("Box ?");
}

#[test]
fn repeated_function_output_patterns_infer_below_binders() {
    repeated("Nat -> ?");
}

#[test]
fn cached_structured_answers_keep_nested_choices_and_priority() {
    checked(
        &seed(),
        r#"structure Box (A : Type) where
  value : A
class Pick (A : outParam Type) where
  stamp : Nat
instance (priority := 500) natural : Pick (Box Nat) := Pick.mk 1
instance (priority := 2000) boolean : Pick (Box Bool) := Pick.mk 2
class Need (A : Type) where
  stamp : Nat
instance needNatural : Need (Box Nat) := Need.mk 9
class Root where
  first : Nat
  second : Nat
instance root {A B : Type} [warm : Pick (Box A)] [pick : Pick (Box B)] [need : Need (Box B)] : Root := Root.mk pick.stamp warm.stamp
def result : Root := inferInstance
theorem resumed : result.first = 1 := by rfl
theorem priority : result.second = 2 := by rfl"#,
    );
}
