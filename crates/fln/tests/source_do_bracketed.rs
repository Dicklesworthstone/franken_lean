//! Braced do uses exactly the native dictionary and dual-checker path.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};

fn limits() -> SourceCheckLimits {
    SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(
        2 * 1024 * 1024,
    )))
}
fn engine() -> Engine {
    let seed = Engine::with_source_seed(limits().admission)
        .unwrap()
        .into_complete()
        .unwrap();
    checked(
        &seed,
        r#"
class Pure (f : Type -> Type) where
  pure : {A : Type} -> A -> f A
class Bind (m : Type -> Type) where
  bind : {A B : Type} -> m A -> (A -> m B) -> m B
def Id (A : Type) : Type := A
instance idPure : Pure Id := { pure := fun a => a }
instance idBind : Bind Id := { bind := fun a k => k a }
"#,
    )
}
fn checked(base: &Engine, source: &str) -> Engine {
    base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|e| panic!("{source}\n{e:?}"))
        .into_complete()
        .unwrap()
        .engine
}

#[test]
fn mixed_braced_and_layout_blocks_have_checked_values() {
    checked(
        &engine(),
        r#"
def nested : Id Nat := do {
  let x ← (do { return 17 });
  let y : Nat := x + 1;
  return (y + 24);
}
theorem nestedValue : nested = 42 := by rfl
def layout : Id Nat := do
  let x ← do { return 41 }
  return (x + 1)
theorem layoutValue : layout = 42 := by rfl
def map {M : Type -> Type} [Pure M] [Bind M] {A B : Type} (f : A -> B) (action : M A) : M B := do { let x ← action; return (f x) }
"#,
    );
}

#[test]
fn braces_do_not_leak_locals_or_admit_ill_typed_actions() {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    for source in [
        "def bad : Id Nat := do { let x ← (do { let hidden := 7; return hidden }); return hidden }",
        "def bad : Id Nat := do { let x : Bool ← (7 : Id Nat); return 0 }",
        "def bad : Id Nat := do { return 7; return 8 }",
        "def bad : Id Nat := do { return 7",
    ] {
        assert!(
            base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
                .is_err(),
            "{source}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
    }
    checked(&base, "def recovery : Id Nat := do { return 42 }");
}
