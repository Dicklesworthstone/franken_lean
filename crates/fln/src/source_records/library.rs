//! Small standard-library source slices for the native headerless environment.
//! These are ordinary proofs, not trusted rewrite rules or parser substitutions.
//! An imported environment and explicit `prelude` never enter this constructor.
use super::*;

pub(super) fn append_lemmas(
    mut engine: Engine,
    limits: EngineAdmissionLimits,
) -> Result<Outcome<Engine>, EngineAdmissionError> {
    // Prelude definitions do not depend on a client's local options, namespace,
    // instances or simp attributes. Publication is a single private transition.
    // The seed's implementation hint is Abbrev, but the pin's source status
    // for List.append is semireducible. Reducible matching must not unfold
    // `[] ++ ?xs` into an unrestricted variable-pattern rewrite.
    engine.environment = fln_elab::reducibility::register(
        &engine.environment,
        &Name::from_components(["List", "append"]),
        fln_elab::reducibility::Reducibility::Semireducible,
    )
    .map_err(|_| EngineAdmissionError::UnexpectedPublication {
        detail: "List.append source reducibility registration failed",
    })?;
    let options = KVMap::new();
    match engine.check_source_files(
        &[include_bytes!("library/list.lean")],
        &options,
        SourceCheckLimits::new(limits),
    ) {
        Ok(Outcome::Complete(checked)) => Ok(Outcome::Complete(checked.engine)),
        Ok(Outcome::Inconclusive(reason)) => Ok(Outcome::Inconclusive(reason)),
        Ok(Outcome::InternalFault(fault)) => Ok(Outcome::InternalFault(fault)),
        Err(error) if error.disposition().2 == 3 => {
            Ok(Outcome::Inconclusive(Inconclusive::dependency_unavailable(
                format!("native List proof-library construction did not complete: {error}"),
            )))
        }
        Err(SourceCheckError::Command { error, .. }) => match *error {
            EngineExecutionError::KernelRejected { class, message } => {
                Err(EngineAdmissionError::KernelRejected { class, message })
            }
            EngineExecutionError::CheckerBridge { detail } => {
                Err(EngineAdmissionError::CheckerBridge { detail })
            }
            _ => Err(EngineAdmissionError::UnexpectedPublication {
                detail: "native List proof-library source failed to elaborate",
            }),
        },
        Err(_) => Err(EngineAdmissionError::UnexpectedPublication {
            detail: "native List proof-library source has invalid command structure",
        }),
    }
}
