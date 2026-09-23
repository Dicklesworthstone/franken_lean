//! Dependent data APIs should compose under the unchanged default runtime budget.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, VmExit};
const VEC: &str = "inductive Vec (A : Type) : Nat -> Type where | nil : Vec A 0 | cons (n : Nat) (head : A) (tail : Vec A n) : Vec A (Nat.succ n)\n";
const APIS: &str = "def first {A : Type} (n : Nat) (xs : Vec A (Nat.succ n)) : A := match xs with | .cons k x tail => x\ndef rest (n : Nat) (xs : Vec Nat (Nat.succ n)) : Vec Nat n := match xs with | .cons k x tail => tail\n";
fn run(source: &str, expected: &str) {
    let limits = EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(EngineAdmissionLimits::new(limits.kernel))
        .unwrap()
        .into_complete()
        .unwrap();
    let batch = engine
        .execute_source_definitions(&[source.as_bytes()], &KVMap::new(), limits)
        .unwrap_or_else(|e| panic!("{source}\n{e:?}"))
        .into_complete()
        .unwrap();
    let VmExit::Returned(value) = &batch.executions.last().unwrap().exit else {
        panic!("returned Nat")
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
        Some(expected)
    );
}
#[test]
fn nested_vector_apis_execute_with_default_preparation_budget() {
    run(
        &format!("{VEC}{APIS}#eval first 0 (rest 1 (Vec.cons 1 7 (Vec.cons 0 42 Vec.nil)))"),
        "42",
    );
}

#[test]
fn multiple_dependent_tail_reconstructions_use_the_default_budget() {
    run(
        &format!(
            "{VEC}{APIS}#eval first 0 (rest 1 (rest 2 (Vec.cons 2 5 (Vec.cons 1 7 (Vec.cons 0 42 Vec.nil)))))"
        ),
        "42",
    );
}

#[test]
fn a_generic_dependent_pipeline_preserves_owned_object_fields() {
    run(
        &format!(
            "{VEC}{APIS}structure Payload where value : Nat\ndef genericRest {{A : Type}} (n : Nat) (xs : Vec A (Nat.succ n)) : Vec A n := match xs with | .cons k x tail => tail\n#eval (first 0 (genericRest 1 (Vec.cons 1 (Payload.mk 7) (Vec.cons 0 (Payload.mk 42) Vec.nil)))).value"
        ),
        "42",
    );
}

#[test]
fn a_real_preparation_stop_preserves_the_logical_input_and_recovers() {
    let limits = EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(EngineAdmissionLimits::new(limits.kernel))
        .unwrap()
        .into_complete()
        .unwrap();
    let options = KVMap::new();
    let definitions = format!("{VEC}{APIS}");
    let source = format!(
        "{definitions}def result : Nat := first 0 (rest 1 (Vec.cons 1 7 (Vec.cons 0 42 Vec.nil)))"
    );
    let root = engine.logical_root(&options);
    let checked = engine
        .check_source_files(
            &[source.as_bytes()],
            &options,
            fln::SourceCheckLimits::new(EngineAdmissionLimits::new(limits.kernel)),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let mut small = limits;
    small.ingress.max_nodes = 500;
    let error = engine
        .execute_source_definitions(&[source.as_bytes()], &options, small)
        .unwrap_err();
    assert!(
        matches!(error, fln::EngineExecutionError::BatchCommand { error, .. }
        if matches!(*error, fln::EngineExecutionError::Ingress(fln_comp::ingress::IngressError::ResourceLimit { .. })))
    );
    assert_eq!(engine.logical_root(&options), root);
    let success = || {
        engine
            .execute_source_definitions(&[source.as_bytes()], &options, limits)
            .unwrap()
            .into_complete()
            .unwrap()
    };
    let first = success();
    let second = success();
    assert_eq!(
        first.engine.logical_root(&options),
        checked.engine.logical_root(&options)
    );
    assert_eq!(
        first.executions.last().unwrap().flbc_artifact,
        second.executions.last().unwrap().flbc_artifact
    );
    assert_eq!(engine.logical_root(&options), root);
}
