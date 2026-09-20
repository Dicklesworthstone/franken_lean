//! Atomic metadata-only instance commands over declarations already admitted by
//! the normal checker council. Names are resolved before their exact identities
//! are recorded; successful entries use the native module journal/replay path.
use super::*;
use fln_elab::source::scope::SourceScope;
use fln_parse::command_scope::instances::InstanceAttribute;

// A single source command must not evade the batch's bounded-work posture by
// containing arbitrarily many metadata updates. The registry also bounds its
// aggregate journal length independently.
const MAX_DECLARATIONS: usize = 4096;

pub(super) fn apply(
    environment: &Environment,
    scope: &SourceScope,
    attribute: InstanceAttribute,
    file: usize,
    command: usize,
    offset: usize,
) -> Result<Environment, SourceCheckError> {
    if attribute.declarations.len() > MAX_DECLARATIONS {
        return Err(SourceCheckError::Limit {
            resource: "instance attribute declarations",
            limit: MAX_DECLARATIONS,
        });
    }
    let mut next = environment.clone();
    for requested in attribute.declarations {
        let name = scope
            .resolve(&requested, |name| next.contains(name))
            .map_err(|error| SourceCheckError::Scope {
                file, command, offset, message: error.to_string(),
            })?
            .ok_or_else(|| SourceCheckError::Scope {
                file, command, offset,
                message: format!("unknown instance declaration `{}`", requested.to_display_string()),
            })?;
        next = fln_elab::instances::set_instance(&next, &name, attribute.priority)
            .map_err(|error| SourceCheckError::Command {
                file, command, offset,
                error: Box::new(EngineExecutionError::Frontend(
                    DefinitionFrontendError::Elaborate(
                        fln_elab::NatDefinitionElabError::Inference(
                            fln_elab::source::SourceInferenceError::InstanceRegistry(error),
                        ),
                    ),
                )),
            })?;
    }
    // A late name/type/registry refusal drops this entire speculative successor.
    Ok(next)
}
