//! Checked propositional decisions execute through the native Boolean runtime row.
#![forbid(unsafe_code)]

use fln::{Budget, ClosedVmValue, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap};

fn execute(source: &[u8]) -> Vec<ClosedVmValue> {
    let limits = EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(EngineAdmissionLimits::new(limits.kernel))
        .unwrap()
        .into_complete()
        .unwrap();
    let completed = engine
        .execute_source_definitions(&[source], &KVMap::new(), limits)
        .unwrap()
        .into_complete()
        .unwrap();
    completed
        .source_evaluation_indices
        .iter()
        .map(|&index| {
            fln::closed_vm_value(&completed.executions[index].exit)
                .unwrap()
                .unwrap()
        })
        .collect()
}

#[test]
fn bool_equality_and_negation_execute() {
    assert_eq!(
        execute(
            br#"
#eval decide (true = true)
#eval decide (true = false)
#eval decide (Not False)
#eval decide (Not True)
"#
        ),
        vec![
            ClosedVmValue::Scalar(1),
            ClosedVmValue::Scalar(0),
            ClosedVmValue::Scalar(1),
            ClosedVmValue::Scalar(0),
        ]
    );
}

#[test]
fn compound_logic_decisions_execute() {
    assert_eq!(
        execute(
            br#"
#eval decide (And True True)
#eval decide (And True False)
#eval decide (Or False True)
#eval decide (False -> False)
#eval decide (Iff True False)
#eval decide (Iff True True)
"#
        ),
        vec![
            ClosedVmValue::Scalar(1),
            ClosedVmValue::Scalar(0),
            ClosedVmValue::Scalar(1),
            ClosedVmValue::Scalar(1),
            ClosedVmValue::Scalar(0),
            ClosedVmValue::Scalar(1),
        ]
    );
}
