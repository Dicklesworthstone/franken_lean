//! Cursor queries use the same checked import closure and command-prefix door
//! as file checking. The unfinished declaration never reaches either admission
//! engine and is never installed into a cache as a completely checked module.
use super::*;
pub use fln_elab::source::inspect::{ObservationKind, ObservedGoal, SourceObservation};
pub use fln_elab::source::scope::SourceScope;
use modules::{
    SourceModuleCheckError, SourceModuleCheckLimits, SourceModuleSession, SourceModuleSessionCheck,
};

/// The prefix is checked; the observation is provisional elaboration state.
/// In particular, `Goals { goals: [] }` is not a proof-checking certificate.
#[derive(Debug)]
pub struct SourceInspection {
    pub prefix: SourceModuleSessionCheck,
    pub scope: SourceScope,
    /// Original source bytes; normalized parser coordinates never escape here.
    pub observation: Option<SourceObservation>,
}

pub(super) fn module(
    session: &mut SourceModuleSession,
    modules: &[SourceModuleInput<'_>],
    entry: &Name,
    offset: usize,
    kind: ObservationKind,
    limits: SourceModuleCheckLimits,
) -> Result<Outcome<SourceInspection>, SourceModuleCheckError> {
    let mut total = 0usize;
    for module in modules {
        total = total
            .checked_add(module.source.len())
            .filter(|bytes| *bytes <= limits.source.max_bytes)
            .ok_or(SourceModuleCheckError::Limit {
                resource: "source bytes",
                limit: limits.source.max_bytes,
            })?;
    }
    let Some(index) = modules.iter().position(|module| module.name == entry) else {
        return Err(SourceModuleCheckError::MissingModule {
            importer: entry.clone(),
            module: entry.clone(),
        });
    };
    let source = modules[index].source;
    let scope_error = |message: &str| SourceModuleCheckError::Source {
        module: entry.clone(),
        error: SourceCheckError::Scope {
            file: 0,
            command: 0,
            offset,
            message: message.to_owned(),
        },
    };
    let text =
        std::str::from_utf8(source).map_err(|_| scope_error("inspection source is not UTF-8"))?;
    if offset > source.len() || !text.is_char_boundary(offset) {
        return Err(scope_error(
            "inspection position is not a source byte boundary",
        ));
    }
    let header =
        modules::parse_source_header(source).map_err(|error| SourceModuleCheckError::Header {
            module: entry.clone(),
            error,
        })?;
    let body = &source[header.body_start.0..];
    let commands = fln_parse::command_scope::partition(body).map_err(|error| {
        SourceModuleCheckError::Header {
            module: entry.clone(),
            error,
        }
    })?;
    if commands.len() > limits.source.max_commands {
        return Err(SourceModuleCheckError::Limit {
            resource: "commands",
            limit: limits.source.max_commands,
        });
    }
    let selected = commands
        .iter()
        .enumerate()
        .rev()
        .find(|(_, (start, _))| header.body_start.0 + start.0 <= offset);
    let prefix_end = selected.map_or(header.body_start.0, |(_, (start, _))| {
        header.body_start.0 + start.0
    });
    let mut inputs = modules.to_vec();
    inputs[index].source = &source[..prefix_end];
    let prefix = match session.check(&inputs, entry)? {
        Outcome::Complete(result) => result,
        Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
        Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
    };
    let environment = prefix.checked.checked.engine.environment();
    let mut scopes = scopes::Scopes::new(environment);
    for (_, command) in commands.iter().take(selected.map_or(0, |(index, _)| index)) {
        if let Some(control) = fln_parse::command_scope::parse(command).map_err(|error| {
            SourceModuleCheckError::Header {
                module: entry.clone(),
                error,
            }
        })? {
            // The original prefix check already applied these immutable journals.
            if matches!(
                control,
                fln_parse::command_scope::ScopeCommand::Simp(_)
                    | fln_parse::command_scope::ScopeCommand::Instance(_)
            ) {
                continue;
            }
            scopes
                .check_limits(&control)
                .map_err(|(resource, limit)| SourceModuleCheckError::Limit { resource, limit })?;
            scopes
                .apply(control)
                .map_err(|message| scope_error(&message))?;
        }
    }
    let mut observation = None;
    if let Some((command_index, (_, command))) = selected {
        let control = fln_parse::command_scope::parse(command).map_err(|error| {
            SourceModuleCheckError::Header {
                module: entry.clone(),
                error,
            }
        })?;
        if control.is_none() {
            let parsed = fln_parse::parse_definition(command).map_err(|error| {
                SourceModuleCheckError::Source {
                    module: entry.clone(),
                    error: SourceCheckError::Command {
                        file: 0,
                        command: command_index,
                        offset: prefix_end + error.primary_offset().map_or(0, |at| at.0),
                        error: Box::new(EngineExecutionError::Frontend(
                            DefinitionFrontendError::Parse(error),
                        )),
                    },
                }
            })?;
            // A CR removed by CRLF normalization has no parser coordinate.
            if let Some(position) = parsed
                .source_view()
                .from_original(fln_parse::BytePos(offset - prefix_end))
            {
                observation = fln_elab::source::inspect::declaration(
                    parsed.syntax(),
                    environment,
                    limits.source.admission.kernel,
                    &scopes.current,
                    position.0,
                    kind,
                )
                .map_err(|error| SourceModuleCheckError::Source {
                    module: entry.clone(),
                    error: SourceCheckError::Command {
                        file: 0,
                        command: command_index,
                        offset: prefix_end,
                        error: Box::new(EngineExecutionError::Frontend(
                            DefinitionFrontendError::Elaborate(error),
                        )),
                    },
                })?;
                if let Some(observation) = &mut observation {
                    let range = match observation {
                        SourceObservation::Goals { range, .. }
                        | SourceObservation::Term { range, .. } => range,
                    };
                    *range = prefix_end
                        + parsed
                            .source_view()
                            .to_original(fln_parse::BytePos(range.start))
                            .0
                        ..prefix_end
                            + parsed
                                .source_view()
                                .to_original(fln_parse::BytePos(range.end))
                                .0;
                }
            }
        }
    }
    Ok(Outcome::Complete(SourceInspection {
        prefix,
        scope: scopes.current,
        observation,
    }))
}
