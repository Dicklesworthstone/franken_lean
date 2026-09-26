//! Anonymous locals cannot act as implicit receivers for unqualified names.
#![forbid(unsafe_code)]
use fln::{
    Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, SourceCheckLimits, VmExit,
};

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn engine() -> Engine {
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}
fn checked(source: &str) {
    engine()
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap();
}

#[test]
fn anonymous_parameters_do_not_intercept_boolean_names() {
    checked(
        "def yes : Nat -> Bool := fun (_ : Nat) => true\ndef no : Nat -> Bool := fun (_ : Nat) => false\ntheorem correct : yes 7 = true := by rfl",
    );
    checked("def yes : Nat -> Bool := fun _ => true\ndef no : Nat -> Bool := fun _ => false");
}

#[test]
fn recursive_boolean_branches_retain_ordinary_name_resolution() {
    let source = b"def even (n : Nat) : Bool := match n with | .zero => true | .succ k => if even k then false else true\n#eval if even 12 then 42 else 0";
    let result = engine()
        .execute_source_definitions(
            &[source],
            &KVMap::new(),
            EngineExecutionLimits::new(limits().kernel),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let VmExit::Returned(value) = &result.executions.last().unwrap().exit else {
        panic!("expected result")
    };
    assert_eq!(fln::nat_decimal(&value.value).as_deref(), Some("42"));
}

#[test]
fn anonymous_records_cannot_supply_missing_identifiers_or_namespace_prefixes() {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    for suffix in [
        "def bad : Box -> Nat := fun (_ : Box) => value",
        "def bad : Box -> Box -> Nat := fun (_ : Box) (_ : Box) => value",
        "def bad : Box -> Nat := fun (_ : Box) => unknown.value",
        "def bad : Box -> Nat := fun (_ : Box) => «unknown.value»",
    ] {
        let source = format!("structure Box where\n  value : Nat\n{suffix}");
        assert!(
            base.check_source_files(
                &[source.as_bytes()],
                &options,
                SourceCheckLimits::new(limits())
            )
            .is_err(),
            "{source}"
        );
        assert_eq!(base.logical_root(&options), root);
        assert!(
            !base
                .environment()
                .contains(&fln::Name::from_components(["bad"]))
        );
        assert!(
            !base
                .environment()
                .contains(&fln::Name::from_components(["Box"]))
        );
    }
}

#[test]
fn named_receivers_exact_constants_and_local_shadowing_still_resolve() {
    checked(
        "structure Box where\n  value : Nat\ndef get : Box -> Box -> Nat := fun (_ : Box) (box : Box) => box.value\ntheorem ok : get { value := 0 } { value := 42 } = 42 := by rfl",
    );
    checked(
        "structure Box where\n  value : Nat\ndef value : Nat := 9\ndef get : Box -> Nat := fun (_ : Box) => value\ntheorem ok : get { value := 42 } = 9 := by rfl",
    );
    checked(
        "structure Box where\n  value : Nat\ndef get : Box -> Nat -> Nat := fun (_ : Box) (value : Nat) => value\ntheorem ok : get { value := 0 } 42 = 42 := by rfl",
    );
}
