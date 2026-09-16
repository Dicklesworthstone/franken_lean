//! Numeric syntax is never permission to manufacture an arbitrary typed value.
#![forbid(unsafe_code)]
use fln_core::outcome::Outcome;
use fln_elab::check_definition_source;
use fln_kernel::verdict::{Budget, Verdict};

#[test]
fn absent_numeric_instances_cannot_manufacture_values_of_arbitrary_types() {
    let budget = Budget::for_stack_bytes(2 * 1024 * 1024);
    let env = fln_elab::seed::bootstrap_nat_environment(budget).unwrap();
    for source in [
        "def bad (A : Type) : A := 7",
        "def bad (A : Type) (x : A) : A := x + x",
        "def bad : Type := 7",
    ] {
        if let Ok(result) = check_definition_source(source.as_bytes(), &env, budget) {
            assert!(
                !matches!(result.outcome, Outcome::Complete(Verdict::Accepted { .. })),
                "{source}"
            );
        }
    }
    let valid = check_definition_source(b"def valid : Nat := 7", &env, budget).unwrap();
    assert!(matches!(valid.outcome, Outcome::Complete(Verdict::Accepted { .. })));
}
