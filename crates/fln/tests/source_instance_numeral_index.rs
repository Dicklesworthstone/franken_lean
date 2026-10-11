//! Numeral keys must preserve the pin's instance selection order.
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

#[test]
fn root_output_reconciliation_cannot_fall_back_to_an_unindexed_numeral_instance() {
    let engine = Engine::with_source_seed(limits().admission)
        .unwrap()
        .into_complete()
        .unwrap();
    let base = checked(
        &engine,
        r#"class D (A : outParam Type) (a : outParam A) where
  value : Nat
instance low : D Nat 7 := D.mk 7
instance high : D Bool true := D.mk 99
class Root where
  value : Nat
instance root {A : Type} {a : A} [warm : D A a] [fixed : D Nat 7] : Root := Root.mk fixed.value"#,
    );
    // Pinned SynthInstance preprocesses only the outer request's outputs.
    // The fixed prerequisite must therefore still select the Nat dictionary,
    // even when an earlier open prerequisite selected the Bool dictionary.
    checked(
        &base,
        "def result : Root := inferInstance\ntheorem valueSelected : result.value = 7 := by rfl",
    );
    let before = base.logical_root(&KVMap::new());
    let error = base
        .check_source_files(
            &[b"def rejected : D Nat 7 := inferInstance"],
            &KVMap::new(),
            limits(),
        )
        .expect_err("the root selects high, whose Bool output cannot reconcile with Nat");
    assert_eq!(error.disposition(), ("elaboration", false, 1));
    assert_eq!(base.logical_root(&KVMap::new()), before);

    // An ascribed numeral, `D Nat (7 : Nat)`, is the same literal key: the pin indexes the
    // elaborated `7`, and refuses this request too (v4.32.0, 2026-10-11).
    let ascribed = checked(
        &engine,
        r#"class D (A : outParam Type) (a : outParam A) where
  value : Nat
instance low : D Nat (7 : Nat) := D.mk 7
instance high : D Bool true := D.mk 99"#,
    );
    let error = ascribed
        .check_source_files(
            &[b"def rejected : D Nat 7 := inferInstance"],
            &KVMap::new(),
            limits(),
        )
        .expect_err("high is tried first, and its Bool output cannot reconcile with Nat");
    assert_eq!(error.disposition(), ("elaboration", false, 1));

    // Registration order within the numeral's discrimination-tree leaf is
    // still significant; correcting literal indexing must not freeze low.
    checked(
        &base,
        r#"instance newest : D Nat 7 := D.mk 42
def result : Root := inferInstance
theorem newestSelected : result.value = 42 := by rfl"#,
    );
}
