//! Universe-only instance goals retain alternatives until their parent completes.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, SourceCheckLimits};

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn seed() -> Engine {
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}
fn checked(base: &Engine, source: &str) -> Engine {
    base.check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits()),
    )
    .unwrap_or_else(|e| panic!("{source}\n{e:?}"))
    .into_complete()
    .unwrap()
    .engine
}
const CLASSES: &str = r#"
class Carrier.{u} : Type u where
  value : Nat
instance low : Carrier.{0} := Carrier.mk 7
instance high : Carrier.{1} := Carrier.mk 99
class Allowed.{u} : Type u where
  value : Nat
instance allowed : Allowed.{0} := Allowed.mk 0
class Root where
  value : Nat
instance root.{u} [c : Carrier.{u}] [valid : Allowed.{u}] : Root := Root.mk c.value
"#;
#[test]
fn later_prerequisite_can_revise_an_earlier_universe_only_choice() {
    let base = checked(&seed(), CLASSES);
    let result = checked(
        &base,
        "def result : Root := inferInstance\ntheorem correct : result.value = 7 := by rfl",
    );
    let batch = result
        .execute_source_definitions(
            &[b"#eval result.value"],
            &KVMap::new(),
            EngineExecutionLimits::new(limits().kernel),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(
        fln::closed_vm_value(&batch.executions.last().unwrap().exit).unwrap(),
        Some(fln::ClosedVmValue::Scalar(7))
    );
}

#[test]
fn cached_universe_choice_resumes_without_changing_an_earlier_sibling() {
    let source = format!(
        "{CLASSES}\nclass PairOut where\n  first : Nat\n  second : Nat\ninstance pair.{{u,v}} [first : Carrier.{{u}}] [second : Carrier.{{v}}] [ok : Allowed.{{v}}] : PairOut := PairOut.mk first.value second.value\n"
    );
    let base = checked(&seed(), &source);
    let result = checked(
        &base,
        "def result : PairOut := inferInstance\ntheorem firstValue : result.first = 99 := by rfl\ntheorem secondValue : result.second = 7 := by rfl",
    );
    let batch = result
        .execute_source_definitions(
            &[b"#eval result.first + result.second"],
            &KVMap::new(),
            EngineExecutionLimits::new(limits().kernel),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(
        fln::closed_vm_value(&batch.executions.last().unwrap().exit).unwrap(),
        Some(fln::ClosedVmValue::Scalar(106))
    );
}

#[test]
fn ground_goals_keep_the_canonical_first_answer_even_when_a_later_premise_fails() {
    let base = checked(
        &seed(),
        r#"
class Fixed where
  value : Nat
instance low : Fixed := Fixed.mk 7
instance high : Fixed := Fixed.mk 99
class Accept (n : Nat) where
  value : Nat
instance seven : Accept 7 := Accept.mk 0
class Result where
  value : Nat
instance result [c : Fixed] [ok : Accept c.value] : Result := Result.mk c.value
"#,
    );
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let source = b"def unpublished : Nat := 42\ndef impossible : Result := inferInstance";
    let error = base
        .check_source_files(&[source], &options, SourceCheckLimits::new(limits()))
        .unwrap_err();
    assert_eq!(error.disposition().0, "elaboration");
    assert_eq!(base.logical_root(&options), root);
    assert!(
        !base
            .environment()
            .contains(&fln::Name::from_components(["unpublished"]))
    );
    checked(
        &base,
        "def chosen : Fixed := inferInstance\ntheorem canonical : chosen.value = 99 := by rfl",
    );
}

#[test]
fn fixed_universe_filters_are_preserved_and_failed_batches_leave_no_assignments() {
    let base = checked(&seed(), CLASSES);
    let options = KVMap::new();
    let root = base.logical_root(&options);
    for source in [
        "def prefix : Nat := 42\ndef missing : Carrier.{2} := inferInstance",
        "def result : Root := inferInstance\ntheorem falseClaim : result.value = 99 := by rfl",
    ] {
        assert!(
            base.check_source_files(
                &[source.as_bytes()],
                &options,
                SourceCheckLimits::new(limits())
            )
            .is_err()
        );
        assert_eq!(base.logical_root(&options), root);
        assert!(
            !base
                .environment()
                .contains(&fln::Name::from_components(["prefix"]))
        );
        assert!(
            !base
                .environment()
                .contains(&fln::Name::from_components(["result"]))
        );
    }
    checked(
        &base,
        "def lowValue : Carrier.{0} := inferInstance\ndef highValue : Carrier.{1} := inferInstance\ndef result : Root := inferInstance\ntheorem chosenLow : lowValue.value = 7 := by rfl\ntheorem chosenHigh : highValue.value = 99 := by rfl\ntheorem recovered : result.value = 7 := by rfl",
    );
}
