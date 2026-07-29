//! G0-4 resource and 1/8/32 productive-partition matrix.

#![forbid(unsafe_code)]

use fln_conformance::syntax_hygiene::{
    BudgetAxis, ContractAttempt, ContractAttemptOutcome, FixtureManifest, SyntaxBudget,
    measure_contract_usage, run_budget_matrix, run_contract_attempt,
};

#[test]
fn syntax_budget_matrix() {
    let manifest = FixtureManifest::load_embedded().expect("manifest");
    let one = run_budget_matrix(&manifest, 1).expect("one-thread matrix");
    let eight = run_budget_matrix(&manifest, 8).expect("eight-thread matrix");
    let thirty_two = run_budget_matrix(&manifest, 32).expect("thirty-two-thread matrix");

    assert_eq!(one.sequence, (0..40).collect::<Vec<_>>());
    assert_eq!(one.sequence, eight.sequence);
    assert_eq!(eight.sequence, thirty_two.sequence);
    assert_eq!(one.stream_root, eight.stream_root);
    assert_eq!(eight.stream_root, thirty_two.stream_root);

    for (threads, matrix) in [(1, one), (8, eight), (32, thirty_two)] {
        assert_eq!(matrix.partitions.len(), threads);
        assert!(
            matrix.partitions.iter().all(|count| *count > 0),
            "{threads} threads must all perform at least one real syntax task"
        );
        assert_eq!(matrix.partitions.iter().sum::<usize>(), 40);
    }
    assert!(run_budget_matrix(&manifest, 0).is_err());
    assert!(run_budget_matrix(&manifest, 2).is_err());
}

#[test]
fn every_budget_and_cancellation_boundary_is_atomic_and_retryable() {
    let manifest = FixtureManifest::load_embedded().expect("manifest");
    let usage = measure_contract_usage(&manifest).expect("manifest-complete usage");
    let exact = SyntaxBudget::exact(&usage);
    let baseline = run_contract_attempt(&usage, &exact, None);
    assert_eq!(baseline.outcome, ContractAttemptOutcome::Complete);
    assert!(baseline.publication_is_valid());

    for axis in BudgetAxis::ALL {
        let observed = usage.observed(*axis);
        assert!(observed > 0, "{axis:?} is a vacuous budget axis");
        let tight = exact.clone().with_limit(*axis, observed - 1);
        let stopped = run_contract_attempt(&usage, &tight, None);
        assert_eq!(
            stopped.outcome,
            ContractAttemptOutcome::Inconclusive {
                axis: *axis,
                allowed: observed - 1,
                observed,
            }
        );
        assert!(
            stopped.publication_is_valid() && stopped.publication_root.is_none(),
            "{axis:?} exhaustion must not publish a partial semantic root"
        );
        let retry = run_contract_attempt(&usage, &exact, None);
        assert_eq!(
            retry, baseline,
            "{axis:?} retry changed the complete result"
        );

        let cancelled = run_contract_attempt(&usage, &exact, Some(*axis));
        assert_eq!(
            cancelled.outcome,
            ContractAttemptOutcome::Cancelled { before: *axis }
        );
        assert!(
            cancelled.publication_is_valid() && cancelled.publication_root.is_none(),
            "{axis:?} cancellation must be nonpublishing"
        );
    }

    let partial_publication_mutant = ContractAttempt {
        outcome: ContractAttemptOutcome::Cancelled {
            before: BudgetAxis::OutputBytes,
        },
        usage_root: baseline.usage_root,
        publication_root: Some("forged-partial-root".to_string()),
    };
    assert!(
        !partial_publication_mutant.publication_is_valid(),
        "a cancellation carrying a semantic publication must be rejected"
    );
}
