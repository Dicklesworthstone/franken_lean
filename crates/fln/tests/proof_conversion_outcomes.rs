//! Proof-conversion nonanswers keep their authority and retry classification.
#![forbid(unsafe_code)]

use fln::{
    Budget, EngineExecutionError, KVMap, Name, NatDefinitionFrontendError, SourceCheckError,
};
use fln_core::expr::{BinderInfo, Expr, FVarId};
use fln_core::level::Level;
use fln_core::outcome::{InternalFault, Outcome};
use fln_elab::NatDefinitionElabError;
use fln_elab::constraint::unify::{UnificationBudget, UnificationError};
use fln_elab::source::SourceInferenceError;
use fln_elab::txn::ElabTxn;
use fln_env::environment::Environment;

fn source_error(error: UnificationError, nested: bool) -> SourceCheckError {
    let mut error = EngineExecutionError::Frontend(NatDefinitionFrontendError::Elaborate(
        NatDefinitionElabError::Inference(SourceInferenceError::Unification(Box::new(error))),
    ));
    if nested {
        error = EngineExecutionError::BatchCommand {
            index: 3,
            error: Box::new(error),
            at: None,
        };
    }
    SourceCheckError::Command {
        file: 1,
        command: 3,
        offset: 17,
        error: Box::new(error),
    }
}

#[test]
fn actual_kernel_proof_comparison_exhaustion_is_not_an_elaboration_verdict() {
    let mut transaction = ElabTxn::new(Environment::new(), KVMap::new(), 7);
    let p = FVarId(Name::from_components(["P"]));
    let h = FVarId(Name::from_components(["h"]));
    let k = FVarId(Name::from_components(["k"]));
    transaction.lctx.add_param(
        p.clone(),
        p.0.clone(),
        Expr::sort(Level::zero()),
        BinderInfo::Default,
    );
    for id in [&h, &k] {
        transaction.lctx.add_param(
            id.clone(),
            id.0.clone(),
            Expr::fvar(p.clone()),
            BinderInfo::Default,
        );
    }
    let before = transaction.clone();
    let mut budget = UnificationBudget::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    budget.kernel = budget.kernel.narrowed(0, budget.kernel.depth);
    let error = transaction
        .unify(&Expr::fvar(h), &Expr::fvar(k), budget)
        .unwrap_err();
    assert!(
        matches!(&error, UnificationError::ConversionCheck { outcome } if matches!(outcome.as_ref(), Outcome::Inconclusive(_)))
    );
    for nested in [false, true] {
        assert_eq!(
            source_error(error.clone(), nested).disposition(),
            ("inconclusive", false, 3)
        );
    }
    assert_eq!(transaction.env, before.env);
    assert_eq!(transaction.mvars, before.mvars);
    assert_eq!(transaction.universes, before.universes);
    assert_eq!(transaction.constraints, before.constraints);
    assert!(transaction.budget.heartbeats_consumed > before.budget.heartbeats_consumed);
}

#[test]
fn conversion_internal_faults_are_not_attributed_to_the_users_proof() {
    let outcome = Outcome::InternalFault(
        InternalFault::new("planted conversion guard fault", "test-only fault")
            .with_evidence("proof-conversion-outcomes"),
    );
    let error = UnificationError::ConversionCheck {
        outcome: Box::new(outcome),
    };
    for nested in [false, true] {
        assert_eq!(
            source_error(error.clone(), nested).disposition(),
            ("internal-fault", false, 4)
        );
    }
}
