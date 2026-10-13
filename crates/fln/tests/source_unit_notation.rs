//! Unit notation uses ordinary admitted constants and their fixed universe.
#![forbid(unsafe_code)]

use fln::{
    Budget, ConstantInfo, Engine, EngineAdmissionLimits, EngineExecutionLimits, Expr, KVMap, Name,
    Outcome, SourceCheckLimits,
};

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}

fn engine() -> Engine {
    // The source seed already provides the admitted polymorphic PUnit family.
    // These ordinary source definitions give the pin's Unit/Unit.unit aliases;
    // no declaration is inserted by notation expansion.
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
        .check_source_files(
            &[b"def Unit := PUnit.{1}\ndef Unit.unit : Unit := PUnit.unit.{1}"],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine
}

#[test]
fn unit_terms_keep_the_global_constant_under_local_and_namespace_shadowing() {
    let source = r#"
def direct := ()
def ascribed : Unit := ((()))
def argument : Unit := (fun (value : Unit) => value) ()
def underLocal (Unit : Nat) : _root_.Unit := ()
namespace Shadow
def Unit := Nat
def Unit.unit : Nat := 91
def nested : _root_.Unit := ()
end Shadow
theorem direct_ok : direct = _root_.Unit.unit := by rfl
theorem argument_ok : argument = _root_.Unit.unit := by rfl
theorem namespace_ok : Shadow.nested = _root_.Unit.unit := by rfl
theorem universe_ok : (() : PUnit.{1}) = PUnit.unit.{1} := by rfl
"#;
    let checked = engine()
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    for label in ["direct", "ascribed", "Shadow.nested"] {
        let Some(ConstantInfo::Defn(definition)) = checked
            .engine
            .environment()
            .find(&Name::from_components(label.split('.')))
        else {
            panic!("a checked source definition");
        };
        assert_eq!(
            definition.value,
            Expr::const_(Name::from_components(["Unit", "unit"]), vec![])
        );
    }
}

#[test]
fn unit_notation_never_invents_an_inhabitant_of_the_expected_type() {
    let engine = engine();
    let options = KVMap::new();
    let root = engine.logical_root(&options);
    for source in [
        "def bad : Nat := ()",
        "def bad : Bool := ()",
        "def bad : PUnit.{0} := ()",
        "def bad : PUnit.{2} := ()",
    ] {
        let result = engine.check_source_files(
            &[source.as_bytes()],
            &options,
            SourceCheckLimits::new(limits()),
        );
        assert!(!matches!(result, Ok(Outcome::Complete(_))), "{source}");
        assert_eq!(engine.logical_root(&options), root);
    }
}

#[test]
fn unit_arguments_execute_through_the_native_checked_source_pipeline() {
    let completed = engine()
        .execute_source_commands_with_checks(
            b"#eval ((fun (_ : Unit) => 42) ())",
            &KVMap::new(),
            EngineExecutionLimits::new(limits().kernel),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let index = completed.batch.source_evaluation_indices[0];
    assert_eq!(
        fln::closed_vm_value(&completed.batch.executions[index].exit).unwrap(),
        Some(fln::ClosedVmValue::Scalar(42))
    );
}
