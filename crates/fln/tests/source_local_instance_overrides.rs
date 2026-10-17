//! Native source-to-council cells for lexical instance priority replacement.
//! These use the native source seed, not pinned Reference artifacts.
#![forbid(unsafe_code)]
use fln::source_check::modules::SourceModuleCheckLimits;
use fln::{
    Budget, ClosedVmValue, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, Name,
    SourceCheckLimits, SourceModuleInput, closed_vm_value,
};

fn admission() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 << 20))
}

fn seed() -> Engine {
    Engine::with_source_seed(admission())
        .unwrap()
        .into_complete()
        .expect("the source seed passes both checkers")
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
fn existing_instance_priorities_can_be_overridden_and_nested_scopes_restore_them() {
    let base = check(&seed(), FIXTURE);
    check(
        &base,
        r#"
theorem initial : read = 9 := by rfl
section
attribute [local instance 2000] low
theorem raised : read = 4 := by rfl
section
attribute [local instance 500] low
theorem lowered : read = 9 := by rfl
end
theorem innerRestored : read = 4 := by rfl
end
theorem outerRestored : read = 9 := by rfl
"#,
    );
}

#[test]
fn equal_priority_local_reregistration_keeps_the_original_preference() {
    let base = check(&seed(), FIXTURE);
    check(
        &base,
        r#"
attribute [local instance] low
theorem sameTie : read = 9 := by rfl
attribute [local instance 2000] low
theorem higherPriority : read = 4 := by rfl
attribute [local instance] low
theorem oldTieRestored : read = 9 := by rfl
"#,
    );
}

#[test]
fn local_registration_reenables_erased_instances_without_changing_tie_order() {
    let base = check(&seed(), FIXTURE);
    check(
        &base,
        r#"
attribute [-instance] high
theorem hidden : read = 4 := by rfl
attribute [local instance] high
theorem visible : read = 9 := by rfl
attribute [-instance] low
attribute [local instance] low
theorem originalOrder : read = 9 := by rfl
"#,
    );
}

#[test]
fn local_to_global_promotion_has_a_separate_preference_in_each_scope() {
    let base = check(&seed(), FIXTURE);
    check(
        &base,
        r#"
section
def first : Marker := Marker.mk 13
attribute [local instance] first
instance second : Marker := Marker.mk 17
theorem beforePromotion : read = 17 := by rfl
attribute [instance] first
theorem sameLocalOrder : read = 17 := by rfl
end
theorem globalOrder : read = 13 := by rfl
"#,
    );
}

#[test]
fn scoped_instances_can_be_overridden_before_and_after_namespace_activation() {
    let base = check(&seed(), FIXTURE);
    check(
        &base,
        r#"
attribute [instance 1500] high
namespace N
scoped instance preferred : Marker := Marker.mk 23
end N
attribute [local instance 2000] N.preferred
theorem explicitLocal : read = 23 := by rfl
open scoped N
theorem namespacePriority : read = 9 := by rfl
attribute [local instance 3000] N.preferred
open scoped N
theorem reopeningDoesNotReset : read = 23 := by rfl
"#,
    );
}

#[test]
fn a_local_override_in_changes_only_the_wrapped_command() {
    let base = check(&seed(), FIXTURE);
    check(
        &base,
        r#"
attribute [local instance 2000] low in
theorem temporarilyLow : read = 4 := by rfl
theorem highAgain : read = 9 := by rfl
"#,
    );
}

#[test]
fn local_overrides_do_not_escape_into_the_environment_or_the_next_file() {
    let base = check(&seed(), FIXTURE);
    let overridden = check(&base, "attribute [local instance 2000] low\n");
    assert_eq!(overridden.environment(), base.environment());
    assert_eq!(
        overridden.logical_root(&KVMap::new()),
        base.logical_root(&KVMap::new())
    );
    check(&overridden, "theorem nextFile : read = 9 := by rfl\n");
    let first = b"attribute [local instance 2000] low\ntheorem firstFile : read = 4 := by rfl\n";
    let second = b"theorem secondFile : read = 9 := by rfl\n";
    base.check_source_files(
        &[first, second],
        &KVMap::new(),
        SourceCheckLimits::new(admission()),
    )
    .unwrap()
    .into_complete()
    .expect("ordered source files restore lexical selection at their boundary");
}

#[test]
fn local_override_batches_refuse_bad_names_and_proofs_without_mutating_the_base() {
    let base = check(&seed(), FIXTURE);
    let root = base.logical_root(&KVMap::new());
    for source in [
        "attribute [local instance 2000] low absent\n",
        "attribute [local instance] read\n",
        "attribute [local instance 2000] low\ntheorem wrong : read = 9 := by rfl\n",
    ] {
        assert!(
            base.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(admission()),
            )
            .is_err(),
            "{source}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
    }
}

#[test]
fn checked_source_execution_observes_overrides_and_restores_outer_dictionaries() {
    let base = check(&seed(), FIXTURE);
    let source = r#"
#eval read
section
attribute [local instance 2000] low
#eval read
section
attribute [local instance 500] low
#eval read
end
#eval read
end
#eval read
"#;
    let completed = base
        .execute_source_commands_with_checks(
            source.as_bytes(),
            &KVMap::new(),
            EngineExecutionLimits::new(admission().kernel),
        )
        .unwrap()
        .into_complete()
        .expect("the checked command stream completes");
    let batch = &completed.batch;
    let values: Vec<_> = batch
        .source_evaluation_indices
        .iter()
        .map(|&index| {
            let value = closed_vm_value(&batch.executions[index].exit).unwrap();
            let Some(ClosedVmValue::Scalar(value)) = value else {
                panic!("the fixture returns a small Nat: {value:?}");
            };
            value
        })
        .collect();
    assert_eq!(values, [9, 4, 9, 4, 9]);
}

#[test]
fn local_priority_overrides_do_not_become_source_module_exports() {
    let base = seed();
    let library = format!(
        "{FIXTURE}\nattribute [local instance 2000] low\n\
         theorem insideLibrary : read = 4 := by rfl\n"
    );
    let names = ["Main", "Lib"].map(|name| Name::from_components([name]));
    let inputs = [
        SourceModuleInput {
            name: &names[0],
            source: b"import Lib\ntheorem importedSelection : read = 9 := by rfl\n",
        },
        SourceModuleInput {
            name: &names[1],
            source: library.as_bytes(),
        },
    ];
    let completed = base
        .check_source_modules(
            &inputs,
            &names[0],
            &KVMap::new(),
            SourceModuleCheckLimits::new(SourceCheckLimits::new(admission())),
        )
        .unwrap()
        .into_complete()
        .expect("both modules pass the checking council");
    assert_eq!(completed.checked.theorems, 2);
    check(
        &completed.checked.engine,
        "theorem nextImport : read = 9 := by rfl\n",
    );
}
