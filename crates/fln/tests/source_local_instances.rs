//! Local instance commands keep their declarations while their registrations follow scope.
#![forbid(unsafe_code)]

use fln::source_check::modules::SourceModuleCheckLimits;
use fln::{
    Budget, ClosedVmValue, DefinitionBatchExecution, Engine, EngineAdmissionLimits,
    EngineExecutionLimits, KVMap, Name, SourceCheckLimits, SourceCommandBatchExecution,
    SourceModuleInput, closed_vm_value,
};

fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn admission() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}

fn limits() -> SourceCheckLimits {
    SourceCheckLimits::new(admission())
}

fn execution_limits() -> EngineExecutionLimits {
    EngineExecutionLimits::new(admission().kernel)
}

fn checked_files(base: &Engine, files: &[&str], expected: &[usize]) -> Engine {
    let mut expected = expected.iter();
    let checked: Vec<String> = files
        .iter()
        .map(|source| {
            let mut checked = String::new();
            for line in source.lines() {
                if let Some(expression) = line.strip_prefix("#eval ") {
                    let value = expected
                        .next()
                        .expect("each evaluation has an expected value");
                    checked.push_str(&format!("example : ({expression}) = {value} := by rfl\n"));
                } else if !line.starts_with("#check ") {
                    checked.push_str(line);
                    checked.push('\n');
                }
            }
            checked
        })
        .collect();
    assert!(
        expected.next().is_none(),
        "every expected value must be checked"
    );
    let sources: Vec<_> = checked.iter().map(|source| source.as_bytes()).collect();
    base.check_source_files(&sources, &KVMap::new(), limits())
        .unwrap_or_else(|error| panic!("{files:?}: {error:?}"))
        .into_complete()
        .expect("both checkers must complete")
        .engine
}

fn assert_named_types(checked: &Engine, executed: &Engine, declarations: &[&str]) {
    for declaration in declarations {
        let declaration = name(declaration);
        let checked = checked.environment().find(&declaration).unwrap();
        let executed = executed.environment().find(&declaration).unwrap();
        assert_eq!(
            checked.constant_val().type_,
            executed.constant_val().type_,
            "the retained named declaration must have the same type: {declaration:?}"
        );
    }
}

fn base() -> Engine {
    let seed = Engine::with_source_seed(admission())
        .unwrap()
        .into_complete()
        .unwrap();
    checked_files(
        &seed,
        &["class Selection where\n  value : Nat\n\
           instance fallbackSelection : Selection := Selection.mk 1\n\
           def selected [Selection] : Nat := Selection.value"],
        &[],
    )
}

fn executed(base: &Engine, source: &str) -> SourceCommandBatchExecution {
    base.execute_source_commands_with_checks(source.as_bytes(), &KVMap::new(), execution_limits())
        .unwrap_or_else(|error| panic!("{source}: {error:?}"))
        .into_complete()
        .expect("the checked command stream must complete")
}

fn evaluated(batch: &DefinitionBatchExecution) -> Vec<usize> {
    batch
        .source_evaluation_indices
        .iter()
        .map(|&index| {
            let value = closed_vm_value(&batch.executions[index].exit).unwrap();
            let Some(ClosedVmValue::Scalar(value)) = value else {
                panic!("these fixtures must return small natural numbers: {value:?}")
            };
            value
        })
        .collect()
}

#[test]
fn nested_local_instances_restore_registration_but_keep_named_constants() {
    let base = base();
    let before = base.logical_root(&KVMap::new());
    let source = r#"#eval selected
section
local instance outerChoice : Selection := Selection.mk 7
#eval selected
section
local instance innerChoice : Selection := Selection.mk 9
#eval selected
end
#eval selected
end
#eval selected
#eval @selected outerChoice
#eval @selected innerChoice
"#;
    let checked = checked_files(&base, &[source], &[1, 7, 9, 7, 1, 7, 9]);
    let completed = executed(&base, source);
    assert_eq!(evaluated(&completed.batch), [1, 7, 9, 7, 1, 7, 9]);
    assert_named_types(
        &checked,
        &completed.batch.engine,
        &["outerChoice", "innerChoice"],
    );
    for constant in ["outerChoice", "innerChoice"] {
        assert!(checked.environment().contains(&name(constant)));
        assert!(!base.environment().contains(&name(constant)));
    }
    assert_eq!(base.logical_root(&KVMap::new()), before);
    assert_eq!(evaluated(&executed(&base, "#eval selected").batch), [1]);
}

#[test]
fn local_instances_index_reducible_aliases_and_restore_their_selection() {
    let seed = Engine::with_source_seed(admission())
        .unwrap()
        .into_complete()
        .unwrap();
    let source = r#"class AliasSelection (A : Type) where
  value : Nat
instance fallbackAliasSelection (A : Type) : AliasSelection A := ⟨1⟩
def aliasSelected (A : Type) [AliasSelection A] : Nat := AliasSelection.value (A := A)
abbrev NatAlias := Nat
abbrev AppliedAlias.{u} (A : Sort u) : Sort u := A
#eval aliasSelected Nat
section
local instance namedAlias : AliasSelection NatAlias := ⟨7⟩
#eval aliasSelected Nat
section
local instance newestAlias : AliasSelection (AppliedAlias NatAlias) := ⟨9⟩
#eval aliasSelected Nat
end
#eval aliasSelected Nat
end
#eval aliasSelected Nat
#eval @aliasSelected Nat namedAlias
"#;
    let checked = checked_files(&seed, &[source], &[1, 7, 9, 7, 1, 7]);
    for alias in ["NatAlias", "AppliedAlias"] {
        assert_eq!(
            fln_elab::reducibility::known_status(checked.environment(), &name(alias)).unwrap(),
            Some(fln_elab::reducibility::Reducibility::Reducible),
            "a source abbrev records its status before local instance indexing"
        );
    }
    let completed = executed(&seed, source);
    assert_eq!(evaluated(&completed.batch), [1, 7, 9, 7, 1, 7]);
    assert_named_types(
        &checked,
        &completed.batch.engine,
        &["namedAlias", "newestAlias"],
    );
    assert_eq!(
        evaluated(&executed(&checked, "#eval aliasSelected Nat").batch),
        [1]
    );
}

#[test]
fn source_abbreviation_effects_preserve_execution_and_explicit_reducibility() {
    use fln_elab::reducibility::{Reducibility, known_status};
    let seed = Engine::with_source_seed(admission())
        .unwrap()
        .into_complete()
        .unwrap();
    let source = b"abbrev aliasValue : Nat := 7";
    let admitted = seed
        .admit_source_declaration(source, &KVMap::new(), admission())
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(
        known_status(admitted.engine.environment(), &name("aliasValue")).unwrap(),
        Some(Reducibility::Reducible)
    );
    let executed = seed
        .execute_source_definition(source, &KVMap::new(), execution_limits())
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(
        closed_vm_value(&executed.exit).unwrap(),
        Some(ClosedVmValue::Scalar(7))
    );
    assert_eq!(
        known_status(executed.engine.environment(), &name("aliasValue")).unwrap(),
        Some(Reducibility::Reducible)
    );
    let explicit = checked_files(&seed, &["@[irreducible] def sealedValue : Nat := 7"], &[]);
    assert_eq!(
        known_status(explicit.environment(), &name("sealedValue")).unwrap(),
        Some(Reducibility::Irreducible)
    );
    for refused in [
        "@[irreducible] abbrev sealedAlias := Nat",
        "abbrev sealedAlias := Nat\nattribute [irreducible] sealedAlias",
    ] {
        assert!(
            seed.check_source_files(&[refused.as_bytes()], &KVMap::new(), limits())
                .is_err(),
            "the pin disallows changing a reducible abbrev to irreducible: {refused}"
        );
    }
}

#[test]
fn local_registrations_preserve_global_priority_and_registration_order() {
    let base = base();
    let source = r#"#eval selected
section
local instance (priority := 500) lowChoice : Selection := Selection.mk 3
#eval selected
local instance (priority := 1000) localChoice : Selection := Selection.mk 7
#eval selected
instance (priority := 1000) laterGlobal : Selection := Selection.mk 9
#eval selected
end
#eval selected
#eval @selected lowChoice
#eval @selected localChoice
"#;
    let checked = checked_files(&base, &[source], &[1, 1, 7, 9, 9, 3, 7]);
    let completed = executed(&base, source);
    assert_eq!(evaluated(&completed.batch), [1, 1, 7, 9, 9, 3, 7]);
    assert_named_types(
        &checked,
        &completed.batch.engine,
        &["lowChoice", "localChoice", "laterGlobal"],
    );
    assert_eq!(evaluated(&executed(&checked, "#eval selected").batch), [9]);
    assert_eq!(evaluated(&executed(&base, "#eval selected").batch), [1]);
}

#[test]
fn file_local_instances_expire_before_later_files_and_successor_calls() {
    let base = base();
    let first = "local instance fileChoice : Selection := Selection.mk 7\n#eval selected";
    let second = "#eval selected\n#eval @selected fileChoice";
    let checked = checked_files(&base, &[first, second], &[7, 1, 7]);
    let completed = base
        .execute_source_definitions(
            &[first.as_bytes(), second.as_bytes()],
            &KVMap::new(),
            execution_limits(),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(evaluated(&completed), [7, 1, 7]);
    assert_named_types(&checked, &completed.engine, &["fileChoice"]);
    for successor in [&checked, &completed.engine] {
        assert!(successor.environment().contains(&name("fileChoice")));
        assert_eq!(
            evaluated(&executed(successor, "#eval selected\n#eval @selected fileChoice").batch),
            [1, 7]
        );
    }
    assert!(!base.environment().contains(&name("fileChoice")));
}

#[test]
fn imported_modules_keep_local_instance_constants_without_exporting_registration() {
    let base = base();
    let before = base.logical_root(&KVMap::new());
    let files = [
        (
            "Main",
            "import Lib\nimport Sibling\n\
             theorem restored : selected = 1 := by rfl\n\
             theorem explicitImported : @selected libraryChoice = 7 := by rfl",
        ),
        (
            "Lib",
            "local instance libraryChoice : Selection := Selection.mk 7\n\
             theorem duringLibrary : selected = 7 := by rfl",
        ),
        ("Sibling", "theorem independent : selected = 1 := by rfl"),
    ];
    let names: Vec<_> = files.iter().map(|(module, _)| name(module)).collect();
    let inputs: Vec<_> = files
        .iter()
        .zip(&names)
        .map(|((_, source), name)| SourceModuleInput {
            name,
            source: source.as_bytes(),
        })
        .collect();
    let completed = base
        .check_source_modules(
            &inputs,
            &name("Main"),
            &KVMap::new(),
            SourceModuleCheckLimits::new(limits()),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(completed.checked.theorems, 4);
    assert!(
        completed
            .checked
            .engine
            .environment()
            .contains(&name("libraryChoice"))
    );
    assert_eq!(
        evaluated(
            &executed(
                &completed.checked.engine,
                "#eval selected\n#eval @selected libraryChoice",
            )
            .batch,
        ),
        [1, 7]
    );
    assert_eq!(base.logical_root(&KVMap::new()), before);
    assert!(!base.environment().contains(&name("libraryChoice")));
}

#[test]
fn rejected_local_instance_streams_leave_no_registration_or_declaration() {
    let base = base();
    let options = KVMap::new();
    let before = base.logical_root(&options);
    for source in [
        "section\nlocal instance temporary : Selection := Selection.mk 7\n\
         theorem falseChoice : selected = 1 := by rfl\nend",
        "local instance temporary : Nat := 7",
    ] {
        assert!(
            base.check_source_files(&[source.as_bytes()], &options, limits())
                .is_err(),
            "{source}"
        );
        assert!(
            base.execute_source_commands_with_checks(
                source.as_bytes(),
                &options,
                execution_limits(),
            )
            .is_err(),
            "{source}"
        );
        assert_eq!(base.logical_root(&options), before);
        assert!(!base.environment().contains(&name("temporary")));
        assert_eq!(evaluated(&executed(&base, "#eval selected").batch), [1]);
    }
}

#[test]
fn local_instances_generalize_parameters_in_their_index_or_instance_prerequisites() {
    // Both programs were independently accepted by the pinned Reference: each
    // `chosen` retains its section argument, and each evaluation returns 42.
    for source in [
        r#"class Selection (n : Nat) where
  value : Nat
section
variable (n : Nat)
local instance : Selection n where
  value := n
def chosen : Nat := Selection.value (n := n)
end
#check chosen
#eval chosen 42
"#,
        r#"class Selection where
  value : Nat
class Input where
  value : Nat
section
variable [input : Input]
local instance : Selection where
  value := input.value
def chosen : Nat := Selection.value
end
#check chosen
#eval @chosen (Input.mk 42)
"#,
    ] {
        let seed = Engine::with_source_seed(admission())
            .unwrap()
            .into_complete()
            .unwrap();
        let before = seed.logical_root(&KVMap::new());
        let checked = checked_files(&seed, &[source], &[42]);
        let completed = executed(&seed, source);
        assert_eq!(evaluated(&completed.batch), [42], "{source}");
        assert_eq!(completed.checks.len(), 1);
        assert_named_types(
            &checked,
            &completed.batch.engine,
            &["Selection", "Selection.value", "chosen"],
        );
        assert!(!seed.environment().contains(&name("chosen")));
        assert_eq!(seed.logical_root(&KVMap::new()), before);
    }
}

#[test]
fn orphan_section_parameters_are_refused_at_the_local_instance_declaration() {
    // The pin refuses this declaration even when no later command attempts
    // instance synthesis: its ordinary `n` cannot be inferred from Selection.
    let source = r#"class Selection where
  value : Nat
section
variable (n : Nat)
local instance : Selection where
  value := n
end
"#;
    let seed = Engine::with_source_seed(admission())
        .unwrap()
        .into_complete()
        .unwrap();
    let options = KVMap::new();
    let before = seed.logical_root(&options);
    let error = seed
        .check_source_files(&[source.as_bytes()], &options, limits())
        .expect_err("an uninferable instance parameter must fail at its declaration");
    assert!(
        matches!(
            &error,
            fln::SourceCheckError::Command {
                file: 0,
                command: 3,
                offset,
                ..
            } if *offset == source.find("local instance").unwrap()
        ),
        "the refusal must identify the local instance, before any query: {error:?}"
    );
    assert!(
        seed.execute_source_commands_with_checks(source.as_bytes(), &options, execution_limits())
            .is_err()
    );
    assert_eq!(seed.logical_root(&options), before);
    assert!(!seed.environment().contains(&name("Selection")));
}
