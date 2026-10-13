//! Source-to-council regression cells for state-only instance erasure.
//! These use the native source seed, not the pinned Reference artifacts.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Name, SourceCheckLimits};
use fln_elab::instances::InstanceRegistry;

fn admission() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 << 20))
}
fn seed() -> Engine {
    Engine::with_source_seed(admission())
        .unwrap()
        .into_complete()
        .unwrap()
}
fn check(base: &Engine, source: &str) -> Engine {
    base.check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(admission()),
    )
    .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
    .into_complete()
    .expect("the checking council completes")
    .engine
}
const FIXTURE: &str = r#"
class Marker where
  value : Nat
instance low : Marker := Marker.mk 4
instance high : Marker := Marker.mk 9
def read [m : Marker] : Nat := @Marker.value m
"#;

#[test]
fn erasure_changes_the_selected_dictionary_and_end_restores_it() {
    let base = check(&seed(), FIXTURE);
    check(
        &base,
        r#"
theorem before : read = 9 := by rfl
section
attribute [-instance] high
theorem inside : read = 4 := by rfl
section
attribute [-instance] low
end
theorem afterInner : read = 4 := by rfl
end
theorem afterOuter : read = 9 := by rfl
"#,
    );
}

#[test]
fn erasure_in_affects_only_its_wrapped_command() {
    let base = check(&seed(), FIXTURE);
    check(
        &base,
        r#"
attribute [-instance] high in
theorem temporarilyLow : read = 4 := by rfl
theorem highAgain : read = 9 := by rfl
"#,
    );
}

#[test]
fn reregistration_restores_availability_without_changing_tie_order() {
    let base = check(&seed(), FIXTURE);
    check(
        &base,
        r#"
attribute [-instance] high
theorem lowSelected : read = 4 := by rfl
attribute [instance] high
theorem highRestored : read = 9 := by rfl
attribute [-instance] low
attribute [instance] low
theorem originalTieOrder : read = 9 := by rfl
"#,
    );
}

#[test]
fn namespace_and_local_instances_can_be_removed_without_exporting_the_removal() {
    let base = check(&seed(), FIXTURE);
    check(
        &base,
        r#"
namespace N
scoped instance preferred : Marker := Marker.mk 12
end N
open scoped N
theorem scopedBefore : read = 12 := by rfl
section
attribute [-instance] N.preferred
theorem scopedHidden : read = 9 := by rfl
local instance temporary : Marker := Marker.mk 15
theorem localBefore : read = 15 := by rfl
attribute [-instance] temporary
theorem localHidden : read = 9 := by rfl
end
theorem scopedRestored : read = 12 := by rfl
"#,
    );
}

#[test]
fn erasure_alone_preserves_the_environment_and_its_logical_root() {
    let base = check(&seed(), FIXTURE);
    let result = check(&base, "attribute [-instance] high\n");
    assert_eq!(result.environment(), base.environment());
    assert_eq!(
        result.logical_root(&KVMap::new()),
        base.logical_root(&KVMap::new())
    );
    assert!(
        InstanceRegistry::read(result.environment())
            .unwrap()
            .is_instance(&Name::from_components(["high"]))
    );
    check(&result, "theorem nextFile : read = 9 := by rfl\n");
}

#[test]
fn erasure_does_not_escape_a_file_in_an_ordered_source_batch() {
    let base = check(&seed(), FIXTURE);
    let first = b"attribute [-instance] high\ntheorem firstFile : read = 4 := by rfl\n";
    let second = b"theorem secondFile : read = 9 := by rfl\n";
    base.check_source_files(
        &[first, second],
        &KVMap::new(),
        SourceCheckLimits::new(admission()),
    )
    .unwrap()
    .into_complete()
    .expect("file boundaries restore lexical selection");
}

#[test]
fn absent_duplicate_and_required_instance_removals_do_not_turn_into_acceptance() {
    let base = check(&seed(), FIXTURE);
    let before = base.logical_root(&KVMap::new());
    for source in [
        "attribute [-instance] absent\n",
        "attribute [-instance] read\n",
        "attribute [-instance] high high\n",
        "attribute [-instance] low high\ndef cannotSynthesize : Nat := read\n",
        "attribute [-instance] high\ntheorem cannotUseRemoved : read = 9 := by rfl\n",
    ] {
        assert!(
            base.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(admission())
            )
            .is_err(),
            "{source}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), before);
    }
}
