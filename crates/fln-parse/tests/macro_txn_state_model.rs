//! State-machine coverage for W4 macro transactions.

#![forbid(unsafe_code)]

use fln_core::mode::Mode;
use fln_core::name::Name;
use fln_core::outcome::Outcome;
use fln_hash::domain::Digest;
use fln_parse::macro_txn::{
    DiagnosticRetention, MacroCapabilities, MacroDiagnostic, MacroInvocationIdentity,
    MacroTxnAbort, MacroTxnBudget, MacroTxnCheckpoint, MacroTxnConfig, MacroTxnError, MacroValue,
    run_macro_transaction,
};
use fln_parse::registry::GrammarEpoch;

fn name(value: &str) -> Name {
    Name::from_components(["Main", value])
}

fn epoch() -> GrammarEpoch {
    GrammarEpoch::from_parts(17, Digest([0x17; 32]))
}

fn identity(label: &str, mode: Mode) -> MacroInvocationIdentity {
    MacroInvocationIdentity::from_canonical_row(
        epoch(),
        mode,
        format!("fln.test.macro-txn-state/1\0{label}").into_bytes(),
    )
}

fn baseline() -> fln_parse::macro_txn::MacroState {
    let mut state = fln_parse::macro_txn::MacroState::new();
    state.insert_environment(name("present"), MacroValue::from_text("old"));
    state.insert_option(name("trace"), MacroValue::from_text("false"));
    state.set_next_gensym(7);
    state
}

#[test]
fn success_failure_cancel_resource_and_nested_restoration() {
    let capabilities = MacroCapabilities::new();

    let mut state = baseline();
    let original = state.clone();
    let success = run_macro_transaction(
        MacroTxnConfig::new(
            identity("success", Mode::Sound),
            &state,
            &capabilities,
            MacroTxnBudget::generous(),
            None,
        ),
        |txn| {
            assert_eq!(
                txn.read_environment(&name("present"))?,
                Some(MacroValue::from_text("old"))
            );
            assert_eq!(txn.read_environment(&name("absent"))?, None);
            txn.set_environment(name("committed"), MacroValue::from_text("root"))?;
            txn.begin_nested()?;
            txn.set_environment(name("rolled-back"), MacroValue::from_text("child"))?;
            txn.set_environment(name("present"), MacroValue::from_text("discarded"))?;
            txn.emit_diagnostic(MacroDiagnostic::new(
                "nested-visible",
                "this diagnostic survives semantic rollback",
                DiagnosticRetention::FailureVisible,
                None,
            ))?;
            txn.emit_diagnostic(MacroDiagnostic::new(
                "nested-private",
                "this diagnostic is speculative",
                DiagnosticRetention::CommitOnly,
                None,
            ))?;
            txn.rollback_nested()?;
            txn.begin_nested()?;
            txn.set_extension(name("extension"), MacroValue::from_text("enabled"))?;
            txn.set_option(name("trace"), MacroValue::from_text("true"))?;
            txn.commit_nested()?;
            assert_eq!(txn.fresh_gensym()?, 7);
            Ok("expanded")
        },
    );

    assert_eq!(state, original, "execution alone must not publish journals");
    let product = match success.into_status() {
        Outcome::Complete(Ok(product)) => product,
        other => panic!("successful transaction was not completed: {other:?}"),
    };
    assert!(
        product
            .diagnostics()
            .iter()
            .any(|diagnostic| diagnostic.code() == "nested-visible")
    );
    assert!(
        product
            .diagnostics()
            .iter()
            .all(|diagnostic| diagnostic.code() != "nested-private")
    );
    let published = product
        .publish(&mut state, &capabilities)
        .expect("unchanged state admits the complete journal");
    assert_eq!(published.value(), &"expanded");
    assert_eq!(
        state.environment(&name("present")),
        Some(&MacroValue::from_text("old"))
    );
    assert_eq!(state.environment(&name("rolled-back")), None);
    assert_eq!(
        state.environment(&name("committed")),
        Some(&MacroValue::from_text("root"))
    );
    assert_eq!(
        state.extension(&name("extension")),
        Some(&MacroValue::from_text("enabled"))
    );
    assert_eq!(
        state.option(&name("trace")),
        Some(&MacroValue::from_text("true"))
    );
    assert_eq!(state.next_gensym(), 8);

    let failure_state = baseline();
    let failure_original = failure_state.clone();
    let failure = run_macro_transaction(
        MacroTxnConfig::new(
            identity("failure", Mode::Sound),
            &failure_state,
            &capabilities,
            MacroTxnBudget::generous(),
            None,
        ),
        |txn| {
            txn.set_environment(name("leak"), MacroValue::from_text("must-not-publish"))?;
            txn.emit_diagnostic(MacroDiagnostic::new(
                "visible",
                "retained failure explanation",
                DiagnosticRetention::FailureVisible,
                None,
            ))?;
            txn.emit_diagnostic(MacroDiagnostic::new(
                "private",
                "discarded speculative explanation",
                DiagnosticRetention::CommitOnly,
                None,
            ))?;
            txn.observe_clock(99)?;
            Ok(())
        },
    );
    assert_eq!(failure_state, failure_original);
    match failure.status() {
        Outcome::Complete(Err(failure)) => {
            assert!(matches!(
                failure.error(),
                MacroTxnError::CapabilityDenied {
                    capability: "clock",
                    mode: Mode::Sound
                }
            ));
            assert_eq!(failure.diagnostics().len(), 1);
            assert_eq!(failure.diagnostics()[0].code(), "visible");
        }
        other => panic!("sound clock read was not a completed refusal: {other:?}"),
    }

    let cancel_state = baseline();
    let cancel_original = cancel_state.clone();
    let cancel_at_publication =
        |checkpoint| matches!(checkpoint, MacroTxnCheckpoint::BeforePublication { .. });
    let cancelled = run_macro_transaction(
        MacroTxnConfig::new(
            identity("cancel", Mode::Faithful),
            &cancel_state,
            &capabilities,
            MacroTxnBudget::generous(),
            Some(&cancel_at_publication),
        ),
        |txn| {
            txn.set_environment(name("cancelled"), MacroValue::from_text("private"))?;
            Ok(())
        },
    );
    assert!(matches!(cancelled.status(), Outcome::Inconclusive(_)));
    assert_eq!(cancel_state, cancel_original);

    let resource_state = baseline();
    let resource_original = resource_state.clone();
    let exhausted = run_macro_transaction(
        MacroTxnConfig::new(
            identity("resource", Mode::Faithful),
            &resource_state,
            &capabilities,
            MacroTxnBudget { max_operations: 0 },
            None,
        ),
        |txn| {
            txn.read_environment(&name("present"))?;
            Ok(())
        },
    );
    assert!(matches!(exhausted.status(), Outcome::Inconclusive(_)));
    assert_eq!(resource_state, resource_original);

    let fault_state = baseline();
    let fault_original = fault_state.clone();
    let faulted: fln_parse::macro_txn::MacroRunReport<()> = run_macro_transaction(
        MacroTxnConfig::new(
            identity("fault", Mode::Faithful),
            &fault_state,
            &capabilities,
            MacroTxnBudget::generous(),
            None,
        ),
        |txn| {
            txn.set_environment(name("fault"), MacroValue::from_text("private"))?;
            Err(MacroTxnAbort::InternalFault(
                fln_core::outcome::InternalFault::new(
                    "FLN-W4-MACRO-TXN-TEST",
                    "deliberate model fault",
                ),
            ))
        },
    );
    assert!(matches!(faulted.status(), Outcome::InternalFault(_)));
    assert_eq!(fault_state, fault_original);
}

#[test]
fn an_unclosed_nested_frame_is_an_internal_fault_and_publishes_nothing() {
    let state = baseline();
    let original = state.clone();
    let report = run_macro_transaction(
        MacroTxnConfig::new(
            identity("unclosed", Mode::Faithful),
            &state,
            &MacroCapabilities::new(),
            MacroTxnBudget::generous(),
            None,
        ),
        |txn| {
            txn.begin_nested()?;
            txn.set_environment(name("private"), MacroValue::from_text("child"))?;
            Ok(())
        },
    );
    assert!(matches!(report.status(), Outcome::InternalFault(_)));
    assert_eq!(state, original);
}
