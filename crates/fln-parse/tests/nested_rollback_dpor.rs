//! Small-state schedule exploration for nested macro transactions.

#![forbid(unsafe_code)]

use fln_core::mode::Mode;
use fln_core::name::Name;
use fln_core::outcome::Outcome;
use fln_hash::domain::{Digest, Domain, hash};
use fln_parse::macro_txn::{
    DiagnosticRetention, MacroCapabilities, MacroDiagnostic, MacroInvocationIdentity, MacroState,
    MacroTxnBudget, MacroTxnCheckpoint, MacroTxnConfig, MacroValue, run_macro_transaction,
};
use fln_parse::registry::GrammarEpoch;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};

fn name(value: &str) -> Name {
    Name::from_components(["Main", value])
}

fn epoch() -> GrammarEpoch {
    GrammarEpoch::from_parts(31, Digest([0x31; 32]))
}

fn identity(label: &str, mode: Mode) -> MacroInvocationIdentity {
    MacroInvocationIdentity::from_canonical_row(
        epoch(),
        mode,
        format!("fln.test.nested-rollback/1\0{label}").into_bytes(),
    )
}

fn all_orders() -> [[usize; 3]; 6] {
    [
        [0, 1, 2],
        [0, 2, 1],
        [1, 0, 2],
        [1, 2, 0],
        [2, 0, 1],
        [2, 1, 0],
    ]
}

fn execute(order: [usize; 3]) -> (Digest, usize, usize) {
    let mut state = MacroState::new();
    state.insert_environment(name("base"), MacroValue::from_text("stable"));
    let capabilities = MacroCapabilities::new();
    let report = run_macro_transaction(
        MacroTxnConfig::new(
            identity("schedule", Mode::Sound),
            &state,
            &capabilities,
            MacroTxnBudget::generous(),
            None,
        ),
        |txn| {
            for operation in order {
                txn.begin_nested()?;
                match operation {
                    0 => {
                        assert_eq!(txn.read_environment(&name("left"))?, None);
                        txn.set_environment(name("left"), MacroValue::from_text("L"))?;
                        txn.commit_nested()?;
                    }
                    1 => {
                        assert_eq!(txn.read_environment(&name("right"))?, None);
                        txn.set_environment(name("right"), MacroValue::from_text("R"))?;
                        txn.commit_nested()?;
                    }
                    2 => {
                        txn.set_environment(name("discarded"), MacroValue::from_text("X"))?;
                        txn.emit_diagnostic(MacroDiagnostic::new(
                            "retained",
                            "rollback is visible without publishing its state",
                            DiagnosticRetention::FailureVisible,
                            None,
                        ))?;
                        txn.emit_diagnostic(MacroDiagnostic::new(
                            "discarded",
                            "speculative child diagnostic",
                            DiagnosticRetention::CommitOnly,
                            None,
                        ))?;
                        txn.rollback_nested()?;
                    }
                    _ => unreachable!("the order domain is exactly three operations"),
                }
            }
            Ok(())
        },
    );
    let product = match report.into_status() {
        Outcome::Complete(Ok(product)) => product,
        other => panic!("schedule did not complete: {other:?}"),
    };
    let read_count = product.reads().observations().len();
    let operation_count = product.operations() as usize;
    assert_eq!(
        product
            .diagnostics()
            .iter()
            .map(|diagnostic| diagnostic.code())
            .collect::<Vec<_>>(),
        vec!["retained"]
    );
    product
        .publish(&mut state, &capabilities)
        .expect("schedule snapshot is unchanged before publication");
    assert_eq!(state.environment(&name("discarded")), None);
    assert_eq!(
        state.environment(&name("left")),
        Some(&MacroValue::from_text("L"))
    );
    assert_eq!(
        state.environment(&name("right")),
        Some(&MacroValue::from_text("R"))
    );
    (state.identity().digest(), read_count, operation_count)
}

#[test]
fn nested_commit_and_rollback_restore_the_exact_state() {
    let observations = all_orders().map(execute);
    for observation in &observations[1..] {
        assert_eq!(
            observation, &observations[0],
            "every dependent-order reduction must reach the same exact state and work population"
        );
    }

    let state = MacroState::new();
    let original = state.clone();
    let cancel = |checkpoint| {
        matches!(
            checkpoint,
            MacroTxnCheckpoint::BeforeOperation { completed: 4 }
        )
    };
    let cancelled = run_macro_transaction(
        MacroTxnConfig::new(
            identity("cancel-mid-child", Mode::Sound),
            &state,
            &MacroCapabilities::new(),
            MacroTxnBudget::generous(),
            Some(&cancel),
        ),
        |txn| {
            txn.begin_nested()?;
            txn.set_environment(name("one"), MacroValue::from_text("1"))?;
            txn.set_environment(name("two"), MacroValue::from_text("2"))?;
            txn.commit_nested()?;
            txn.set_environment(name("never"), MacroValue::from_text("published"))?;
            Ok(())
        },
    );
    assert!(matches!(cancelled.status(), Outcome::Inconclusive(_)));
    assert_eq!(state, original);
}

fn thread_reduction(worker_count: usize) -> (Digest, usize) {
    let tasks = 96usize;
    let next = Arc::new(AtomicUsize::new(0));
    let roots = Arc::new(Mutex::new(Vec::new()));
    std::thread::scope(|scope| {
        for _ in 0..worker_count {
            let next = Arc::clone(&next);
            let roots = Arc::clone(&roots);
            scope.spawn(move || {
                let mut local = Vec::new();
                loop {
                    let task = next.fetch_add(1, Ordering::Relaxed);
                    if task >= tasks {
                        break;
                    }
                    let order = all_orders()[task % all_orders().len()];
                    local.push(execute(order).0);
                }
                roots
                    .lock()
                    .expect("worker result lock is not poisoned")
                    .extend(local);
            });
        }
    });
    let mut roots = Arc::try_unwrap(roots)
        .expect("all worker references were joined")
        .into_inner()
        .expect("worker result lock is not poisoned");
    assert_eq!(roots.len(), tasks, "the reduction must be productive");
    roots.sort();
    let mut canonical = Vec::with_capacity(roots.len() * 32);
    for root in &roots {
        canonical.extend_from_slice(&root.0);
    }
    (hash(Domain::Fixture, &canonical), roots.len())
}

#[test]
fn productive_one_eight_and_thirty_two_reductions_match() {
    let one = thread_reduction(1);
    let eight = thread_reduction(8);
    let thirty_two = thread_reduction(32);
    assert_eq!(one.1, 96);
    assert_eq!(one, eight);
    assert_eq!(one, thirty_two);
}
