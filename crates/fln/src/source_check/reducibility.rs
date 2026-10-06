//! Global source reducibility updates over already checked declarations.
//!
//! Validation follows the pin's Lean/ReducibilityAttrs.lean:126–158. A global
//! attribute is restricted to this file and to the permitted previous statuses;
//! it is not an unrestricted setter for the imported reducibility journal.
use super::*;
use fln_elab::reducibility::{Reducibility, ReducibilityError};
use fln_elab::source::scope::SourceScope;
use fln_parse::command_scope::reducibility::{
    AttributeScope, ReducibilityAttribute, ReducibilityStatus,
};

const MAX_DECLARATIONS: usize = 4096;

pub(super) fn registry_error(
    error: ReducibilityError,
    (file, command, offset): (usize, usize, usize),
) -> SourceCheckError {
    SourceCheckError::Command {
        file,
        command,
        offset,
        error: Box::new(EngineExecutionError::Frontend(
            DefinitionFrontendError::Elaborate(fln_elab::NatDefinitionElabError::Inference(
                fln_elab::source::SourceInferenceError::Unification(Box::new(
                    fln_elab::constraint::unify::UnificationError::Reducibility(error),
                )),
            )),
        )),
    }
}

pub(super) fn apply(
    environment: &Environment,
    file_base: &Environment,
    scope: &SourceScope,
    attribute: ReducibilityAttribute,
    position @ (file, command, offset): (usize, usize, usize),
) -> Result<Environment, SourceCheckError> {
    if attribute.declarations.len() > MAX_DECLARATIONS {
        return Err(SourceCheckError::Limit {
            resource: "reducibility attribute declarations",
            limit: MAX_DECLARATIONS,
        });
    }
    let refuse = |message| SourceCheckError::Scope {
        file,
        command,
        offset,
        message,
    };
    match attribute.scope {
        AttributeScope::Local => {
            return Err(refuse(
                "local reducibility attributes require lexical restoration, which is not yet implemented".into(),
            ));
        }
        AttributeScope::Scoped => {
            return Err(refuse(if scope.namespace.is_anonymous() {
                "scoped reducibility attributes must be used inside namespaces".into()
            } else {
                "failed to set reducibility status: the scoped modifier is not recommended for this kind of attribute".into()
            }));
        }
        AttributeScope::Global => {}
    }
    let status = match attribute.status {
        ReducibilityStatus::Reducible => Reducibility::Reducible,
        ReducibilityStatus::Semireducible => Reducibility::Semireducible,
        ReducibilityStatus::Irreducible => Reducibility::Irreducible,
        ReducibilityStatus::ImplicitReducible => Reducibility::ImplicitReducible,
    };
    let mut next = environment.clone();
    for requested in attribute.declarations {
        let name = scope
            .resolve(&requested, |name| next.contains(name))
            .map_err(|error| refuse(error.to_string()))?
            .ok_or_else(|| {
                refuse(format!(
                    "unknown reducibility declaration `{}`",
                    requested.to_display_string(),
                ))
            })?;
        if !matches!(next.find(&name), Some(ConstantInfo::Defn(_))) {
            return Err(refuse(format!(
                "failed to set reducibility status: `{}` is not a definition",
                name.to_display_string(),
            )));
        }
        if file_base.contains(&name) {
            return Err(refuse(format!(
                "failed to set reducibility status: `{}` has not been defined in this file",
                name.to_display_string(),
            )));
        }
        let old = fln_elab::reducibility::table(&next)
            .map_err(|error| registry_error(error, position))?
            .status(&name);
        let allowed = match status {
            Reducibility::Reducible | Reducibility::ImplicitReducible => {
                old == Reducibility::Semireducible
            }
            Reducibility::Irreducible => {
                matches!(
                    old,
                    Reducibility::Semireducible | Reducibility::ImplicitReducible
                )
            }
            Reducibility::Semireducible => false,
        };
        if !allowed {
            return Err(refuse(format!(
                "failed to set reducibility status for `{}`: transition from {old:?} to {status:?} is not permitted",
                name.to_display_string(),
            )));
        }
        next = fln_elab::reducibility::register(&next, &name, status)
            .map_err(|error| registry_error(error, position))?;
    }
    // The whole command succeeds before the batch can observe this successor.
    Ok(next)
}
