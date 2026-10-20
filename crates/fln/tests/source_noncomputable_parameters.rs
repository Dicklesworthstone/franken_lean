//! Static datatype parameters survive source checking through native execution.
//! These use ordinary match syntax, not the frontier-only direct-recursion lane.
#![forbid(unsafe_code)]
use fln::{
    Budget, ClosedVmValue, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, Name,
    SourceCheckLimits, closed_vm_value,
};

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}

fn base() -> Engine {
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
        .check_source_files(
            &[br#"
noncomputable def hiddenParameter : Nat := 5
inductive ParamMatch (n : Nat) where
  | mk (value : Nat)
inductive ParamChoice (n m : Nat) where
  | left (value : Nat)
  | right (value : Nat)
inductive ProofMatch (n : Nat) where
  | mk (proof : n = n) (value : Nat)
noncomputable def hiddenCarrier : ParamMatch 5 := @ParamMatch.mk 5 42
def ordinary (n value : Nat) : Nat := value
"#],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine
}

fn run(base: &Engine, source: &str) -> fln::DefinitionBatchExecution {
    let root = base.logical_root(&KVMap::new());
    let result = base
        .execute_source_definitions(
            &[source.as_bytes()],
            &KVMap::new(),
            EngineExecutionLimits::new(limits().kernel),
        )
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap();
    assert_eq!(base.logical_root(&KVMap::new()), root);
    result
}

fn returns_42(base: &Engine, source: &str) {
    let result = run(base, source);
    let execution = result.executions.last().expect("a real VM execution");
    assert_eq!(
        closed_vm_value(&execution.exit).unwrap(),
        Some(ClosedVmValue::Scalar(42)),
        "{source}"
    );
}

fn refuses(base: &Engine, source: &str, reason: &str) {
    let root = base.logical_root(&KVMap::new());
    let error = match base.execute_source_definitions(
        &[source.as_bytes()],
        &KVMap::new(),
        EngineExecutionLimits::new(limits().kernel),
    ) {
        Err(error) => error,
        Ok(_) => panic!("accepted an executable dependency: {source}"),
    };
    let message = error.to_string();
    assert!(message.contains(reason), "{source}\n{message}");
    assert_eq!(base.logical_root(&KVMap::new()), root);
}

#[test]
fn constructing_and_matching_a_noncomputable_parameter_reaches_the_vm() {
    let engine = base();
    returns_42(
        &engine,
        r#"
def matched : Nat :=
  match (@ParamMatch.mk hiddenParameter 42) with
  | .mk value => value
#eval matched
"#,
    );
    assert!(
        !engine
            .environment()
            .contains(&Name::from_components(["matched"]))
    );
}

#[test]
fn multiple_parameters_do_not_change_variant_selection_or_minor_execution() {
    let engine = base();
    for source in [
        r#"
#eval match (@ParamChoice.left hiddenParameter (hiddenParameter + 1) 42) with
  | .left value => value
  | .right value => value + 1
"#,
        r#"
#eval match (@ParamChoice.right hiddenParameter (hiddenParameter + 1) 41) with
  | .left value => value
  | .right value => value + 1
"#,
    ] {
        returns_42(&engine, source);
    }
}

#[test]
fn captured_runtime_values_can_occur_only_in_the_erased_parameter() {
    returns_42(
        &base(),
        r#"
#eval (fun (n : Nat) =>
  match (@ParamMatch.mk (n + hiddenParameter) 42) with
  | .mk value => value) 7
"#,
    );
}

#[test]
fn dependent_proof_fields_are_erased_under_the_original_parameter() {
    returns_42(
        &base(),
        r#"
#eval match (@ProofMatch.mk hiddenParameter (Eq.refl hiddenParameter) 42) with
  | .mk proof value => value
"#,
    );
}

#[test]
fn a_partially_applied_constructor_retains_its_runtime_field_interface() {
    returns_42(
        &base(),
        r#"
#eval let make : Nat -> ParamMatch hiddenParameter := @ParamMatch.mk hiddenParameter
  match make 42 with
  | .mk value => value
"#,
    );
}

#[test]
fn erased_parameters_do_not_hide_live_fields_minors_or_majors() {
    let engine = base();
    for (source, dependency) in [
        (
            r#"
#eval match (@ParamMatch.mk hiddenParameter hiddenParameter) with
  | .mk value => value
"#,
            "hiddenParameter",
        ),
        (
            r#"
#eval match (@ParamMatch.mk hiddenParameter 42) with
  | .mk value => hiddenParameter
"#,
            "hiddenParameter",
        ),
        (
            r#"
#eval match hiddenCarrier with
  | .mk value => value
"#,
            "hiddenCarrier",
        ),
    ] {
        refuses(&engine, source, "noncomputable");
        refuses(&engine, source, dependency);
    }
    returns_42(
        &engine,
        "#eval match (@ParamMatch.mk hiddenParameter 42) with | .mk value => value",
    );
}

#[test]
fn ordinary_arguments_and_strict_let_initializers_do_not_become_static() {
    let engine = base();
    for source in [
        "#eval ordinary hiddenParameter 42",
        r#"
#eval let parameter : Nat := hiddenParameter
  match (@ParamMatch.mk parameter 42) with
  | .mk value => value
"#,
        r#"
noncomputable section
#eval match (@ParamMatch.mk hiddenParameter hiddenParameter) with
  | .mk value => value
end
"#,
    ] {
        refuses(&engine, source, "noncomputable");
    }
}

#[test]
fn static_parameters_do_not_enable_explicitly_unsupported_recursors() {
    refuses(
        &base(),
        r#"
#eval @ParamMatch.rec hiddenParameter (fun _ => Nat) (fun value => value)
  (@ParamMatch.mk hiddenParameter 42)
"#,
        "code generator does not support recursor `ParamMatch.rec`",
    );
}
