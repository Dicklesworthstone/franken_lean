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
    if attribute.scoped && scope.namespace.is_anonymous() {
        return Err(SourceCheckError::Scope {
            file,
            command,
            offset,
            message: "scoped instances require a non-root namespace".into(),
        });
    }
    let mut next = environment.clone();
    for requested in attribute.declarations {
        let name = scope
            .resolve(&requested, |name| next.contains(name))
            .map_err(|error| SourceCheckError::Scope {
                file,
                command,
                offset,
                message: error.to_string(),
            })?
            // The pin's words for a name nothing resolves (`realizeGlobalConstNoOverload`):
            // the name as written, measured with plain, dotted and namespaced names.
            .ok_or_else(|| SourceCheckError::Scope {
                file,
                command,
                offset,
                message: format!("Unknown constant `{}`", requested.to_display_string()),
            })?;
        // The standalone attribute does not acquire the `instance` command's
        // implicitReducible default (Lean/ReducibilityAttrs.lean:205–220).
        // Preserve an unrecorded declaration's previous status before the
        // registry's native-instance fallback can start treating it as one.
        let statuses = fln_elab::reducibility::table(&next)
            .map_err(|error| reducibility::registry_error(error, (file, command, offset)))?;
        let unrecorded_status = statuses
            .get(&name)
            .is_none()
            .then(|| statuses.status(&name));
        next = if attribute.scoped {
            fln_elab::instances::scoped::register(
                &next,
                &scope.namespace,
                &name,
                attribute.priority,
            )
        } else {
            fln_elab::instances::set_instance(&next, &name, attribute.priority)
        }
        .map_err(|error| SourceCheckError::Command {
            file,
            command,
            offset,
            error: Box::new(EngineExecutionError::Frontend(
                DefinitionFrontendError::Elaborate(fln_elab::NatDefinitionElabError::Inference(
                    fln_elab::source::SourceInferenceError::InstanceRegistry(error),
                )),
            )),
        })?;
        if let Some(status) = unrecorded_status {
            next = fln_elab::reducibility::register(&next, &name, status)
                .map_err(|error| reducibility::registry_error(error, (file, command, offset)))?;
        }
    }
    // A late name/type/registry refusal drops this entire speculative successor.
    Ok(next)
}
