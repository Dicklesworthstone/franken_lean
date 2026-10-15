//! Carry observations alongside, never instead of, checked declaration effects.
//!
//! Attributed and noncomputable definitions use the same scoped elaborator and
//! admission path as unobserved definitions. Trace capture is not a reason to
//! compile a noncomputable body or skip any instance/attribute journal update.

use super::*;

/// A rendered raw trace at its original source location. It carries no proof authority.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceTraceMessage {
    pub command_index: usize,
    pub at: fln_parse::BytePos,
    pub message: String,
}

/// Freeze display in the command's environment and scope, not the final file's.
/// The batch bound also applies to messages that a later guard chooses to drop.
pub(crate) fn append(
    messages: &mut Vec<SourceTraceMessage>,
    bytes: &mut usize,
    traces: Vec<fln_elab::source::trace::SourceTrace>,
    parsed: &fln_parse::ParsedSourceCommand,
    environment: &Environment,
    command_index: usize,
    offset: fln_parse::BytePos,
) -> Result<(), EngineExecutionError> {
    const MAX_MESSAGES: usize = 4096;
    const MAX_BYTES: usize = 16 * 1024 * 1024;
    for trace in traces {
        if messages.len() >= MAX_MESSAGES {
            return Err(EngineExecutionError::SourceScopeLimit {
                resource: "raw tactic trace messages",
                limit: MAX_MESSAGES,
            });
        }
        let message = crate::pretty::goals::render(environment, &trace)
            .map_err(|problem| EngineExecutionError::NotImplemented { feature: problem.0 })?;
        *bytes = bytes
            .checked_add(message.len())
            .and_then(|n| n.checked_add(1))
            .filter(|n| *n <= MAX_BYTES)
            .ok_or(EngineExecutionError::SourceScopeLimit {
                resource: "raw tactic trace bytes",
                limit: MAX_BYTES,
            })?;
        let local = parsed
            .source_view()
            .to_original(fln_parse::BytePos(trace.at));
        let at =
            offset
                .0
                .checked_add(local.0)
                .ok_or(EngineExecutionError::UnexpectedPublication {
                    detail: "raw tactic trace source offset overflow",
                })?;
        messages.push(SourceTraceMessage {
            command_index,
            at: fln_parse::BytePos(at),
            message,
        });
    }
    Ok(())
}

pub(crate) struct ObservedSourceAdmission {
    pub(crate) admission: DeclarationBatchAdmission,
    pub(crate) traces: Vec<fln_elab::source::trace::SourceTrace>,
}

impl Engine {
    pub(crate) fn admit_observed_source_definition(
        &self,
        parsed: &fln_parse::ParsedSourceCommand,
        options: &KVMap,
        limits: EngineAdmissionLimits,
        scope: &fln_elab::source::scope::SourceScope,
    ) -> Result<Outcome<ObservedSourceAdmission>, EngineExecutionError> {
        // These routes may synthesize several declarations in separate
        // contexts. Until their observations have a shared owner, do not drop
        // them or feed their syntax to the single-declaration elaborator.
        if parsed.kind() != fln_parse::SourceCommandKind::Definition
            || fln_elab::source::is_record(parsed.syntax())
            || fln_elab::source::is_inductive(parsed.syntax())
            || fln_elab::source::partial::is_partial(parsed.syntax())
        {
            return Err(EngineExecutionError::NotImplemented {
                feature: "raw tactic traces from inductive, record or partial declaration batches",
            });
        }
        let elaborated = match elaboration_outcome(fln_elab::source::trace::elaborate_definition(
            parsed.syntax(),
            self.environment(),
            limits.kernel,
            scope,
        ))? {
            Outcome::Complete(elaborated) => elaborated,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        let traces = elaborated.traces;
        let elaborated = elaborated.candidate;
        // This checks the entire declaration with both checkers, then replays
        // exactly its instance, simp, reducibility, protection and inferred or
        // explicit noncomputable effects. No trace grants publication authority.
        Ok(
            match self.admit_scoped_candidate(
                parsed.syntax(),
                elaborated.declaration,
                elaborated.irreducible,
                elaborated.noncomputable,
                options,
                limits,
                scope,
            )? {
                Outcome::Complete(admission) => {
                    Outcome::Complete(ObservedSourceAdmission { admission, traces })
                }
                Outcome::Inconclusive(reason) => Outcome::Inconclusive(reason),
                Outcome::InternalFault(fault) => Outcome::InternalFault(fault),
            },
        )
    }

    pub(crate) fn check_observed_source_example(
        &self,
        parsed: ParsedSourceCommand,
        options: &KVMap,
        limits: EngineAdmissionLimits,
        command_index: usize,
        scope: &fln_elab::source::scope::SourceScope,
    ) -> Result<
        Outcome<(SourceCheck, Vec<fln_elab::source::trace::SourceTrace>)>,
        EngineExecutionError,
    > {
        let name = fresh_generated_command_name(self.environment(), command_index)?;
        let (declaration, traces) =
            match elaboration_outcome(fln_elab::source::trace::elaborate_example(
                parsed.syntax(),
                name,
                self.environment(),
                limits.kernel,
                scope,
            ))? {
                Outcome::Complete(value) => value,
                Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
            };
        let Declaration::Defn(definition) = &declaration else {
            return Err(EngineExecutionError::UnexpectedPublication {
                detail: "observed example returned a non-definition candidate",
            });
        };
        let checked_type = definition.base.type_.clone();
        Ok(self
            .admit_declaration(declaration, options, limits)?
            .map_complete(|admission| {
                (
                    SourceCheck {
                        parsed,
                        declaration: admission.declaration,
                        checked_type,
                        environment_root: admission.base_logical_root,
                        checker: admission.checker,
                        scope: scope.clone(),
                    },
                    traces,
                )
            }))
    }
}
