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
fn repeated_unknown_semi_outputs_share_answers_and_keep_known_output_filters() {
    let mut source = String::from(
        "class Semi0 (A : semiOutParam Type) where\n  value : Nat\ninstance semi0 : Semi0 Nat := Semi0.mk 7\n",
    );
    for depth in 1..=12 {
        let previous = depth - 1;
        source.push_str(&format!(
            "class Semi{depth} (A : semiOutParam Type) where\n  value : Nat\ninstance semi{depth} {{A B : Type}} [first : Semi{previous} A] [second : Semi{previous} B] : Semi{depth} Nat := Semi{depth}.mk first.value\n"
        ));
    }
    let base = checked(&engine(), &source);
    checked(
        &base,
        "def result : Semi12 Nat := inferInstance\ntheorem correct : result.value = 7 := by rfl",
    );
    assert!(
        base.check_source_files(
            &[b"def bad : Semi12 Bool := inferInstance"],
            &KVMap::new(),
            limits(),
        )
        .is_err()
    );
}

#[test]
fn fresh_semi_output_cycle_can_use_a_productive_base_instance() {
    checked(
        &engine(),
        r#"class Choose (A : semiOutParam Type) where
  tag : Nat
instance (priority := 500) base : Choose Nat := Choose.mk 7
instance (priority := 2000) step {A : Type} [next : Choose A] : Choose Bool := Choose.mk (next.tag + 1)
def result : Choose Bool := inferInstance
theorem cycleRecovered : result.tag = 8 := by rfl"#,
    );
}

#[test]
fn cached_semi_output_choices_backtrack_without_restricting_later_fresh_goals() {
    checked(
        &engine(),
        r#"class Choice (A : semiOutParam Type) where
  tag : Nat
instance (priority := 500) boolean : Choice Bool := Choice.mk 8
instance (priority := 2000) natural : Choice Nat := Choice.mk 7
class NeedsBool (A : Type) where
  tag : Nat
instance needsBool : NeedsBool Bool := NeedsBool.mk 1
class Root where
  value : Nat
instance root {A B C : Type} [first : Choice A] [second : Choice B] [need : NeedsBool B] [third : Choice C] [fixed : Choice Bool] : Root := Root.mk (first.tag * 1000 + second.tag * 100 + third.tag * 10 + fixed.tag)
def result : Root := inferInstance
theorem recovered : result.value = 7878 := by rfl"#,
    );
}

#[test]
fn semi_output_cycle_failure_is_a_missing_instance_and_recovers_after_registration() {
    let base = checked(
        &engine(),
        "class Choose (A : semiOutParam Type) where\n  tag : Nat\ninstance step {A : Type} [next : Choose A] : Choose Bool := Choose.mk (next.tag + 1)",
    );
    let before = base.logical_root(&KVMap::new());
    let error = base
        .check_source_files(
            &[b"def bad : Choose Bool := inferInstance"],
            &KVMap::new(),
            limits(),
        )
        .unwrap_err();
    assert_eq!(error.disposition(), ("elaboration", false, 1));
    assert_eq!(before, base.logical_root(&KVMap::new()));
    checked(
        &base,
        "instance base : Choose Nat := Choose.mk 7\ndef result : Choose Bool := inferInstance\ntheorem recovered : result.tag = 8 := by rfl",
    );
}

#[test]
fn structured_semi_outputs_share_substitutions_without_erasing_their_shape() {
    let mut source = String::from(
        "structure Box (A : Type) where\n  value : A\nclass Tree0 (A : semiOutParam Type) where\n  tag : Nat\ninstance tree0 : Tree0 (Box Nat) := Tree0.mk 7\n",
    );
    for depth in 1..=12 {
        let previous = depth - 1;
        source.push_str(&format!("class Tree{depth} (A : semiOutParam Type) where\n  tag : Nat\ninstance tree{depth} {{A B : Type}} [first : Tree{previous} (Box A)] [second : Tree{previous} (Box B)] : Tree{depth} (Box Nat) := Tree{depth}.mk first.tag\n"));
    }
    let base = checked(&engine(), &source);
    checked(
        &base,
        "def result : Tree12 (Box Nat) := inferInstance\ntheorem correct : result.tag = 7 := by rfl",
    );
    assert!(
        base.check_source_files(
            &[b"def bad : Tree12 (Box Bool) := inferInstance"],
            &KVMap::new(),
            limits()
        )
        .is_err()
    );
}

#[test]
fn structured_variant_cycles_reach_the_base_without_confusing_fixed_outputs() {
    checked(
        &engine(),
        r#"structure Box (A : Type) where
  value : A
class Choose (A : semiOutParam Type) where
  tag : Nat
instance (priority := 500) base : Choose (Box Nat) := Choose.mk 7
instance (priority := 2000) step {A : Type} [next : Choose (Box A)] : Choose (Box Bool) := Choose.mk (next.tag + 1)
def result : Choose (Box Bool) := inferInstance
theorem recovered : result.tag = 8 := by rfl"#,
    );
}
