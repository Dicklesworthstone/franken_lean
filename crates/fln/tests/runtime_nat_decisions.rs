//! Checked equality dictionaries reach the existing Nat row through real source.
#![forbid(unsafe_code)]

use fln::{Budget, ClosedVmValue, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap};

#[test]
fn checked_nat_decisions_execute_large_operands_and_captured_infix_arguments() {
    let limits = EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(EngineAdmissionLimits::new(limits.kernel))
        .unwrap()
        .into_complete()
        .unwrap();
    let source = br#"
def same (a b : Nat) : Bool := decide (a = b)
#eval same 18446744073709551616 (18446744073709551616 + 0)
#eval same 18446744073709551616 (18446744073709551616 + 1)
#eval let bump := fun (n : Nat) => n + 1; bump 18446744073709551616 == 18446744073709551617
#eval decide (18446744073709551616 = 18446744073709551616)
#eval let a := 18446744073709551616; let b := a + 1; a == b
"#;
    let completed = engine
        .execute_source_definitions(&[source], &KVMap::new(), limits)
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(completed.executions.len(), 6);
    assert_eq!(completed.source_evaluation_indices, [1, 2, 3, 4, 5]);
    for execution in &completed.executions {
        fln_comp::flbc::decode_canonical(&execution.flbc_artifact, limits.flbc_codec)
            .expect("executed equality artifact remains canonical");
    }
    let values: Vec<_> = completed
        .source_evaluation_indices
        .iter()
        .map(|&index| {
            let execution = &completed.executions[index];
            fln::closed_vm_value(&execution.exit)
                .unwrap()
                .unwrap_or_else(|| {
                    panic!(
                        "evaluation {index} returned unsupported type {:?}",
                        execution.runtime_type
                    )
                })
        })
        .collect();
    assert_eq!(
        values,
        vec![
            ClosedVmValue::Scalar(1),
            ClosedVmValue::Scalar(0),
            ClosedVmValue::Scalar(1),
            ClosedVmValue::Scalar(1),
            ClosedVmValue::Scalar(0),
        ]
    );
}
