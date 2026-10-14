//! Carry observations alongside, never instead of, checked declaration effects.
//!
//! Attributed and noncomputable definitions use the same scoped elaborator and
//! admission path as unobserved definitions. Trace capture is not a reason to
//! compile a noncomputable body or skip any instance/attribute journal update.

use super::*;

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
        let elaborated =
            match elaboration_outcome(fln_elab::source::scope::elaborate_definition_with_effects(
                parsed.syntax(),
                self.environment(),
                limits.kernel,
                scope,
            ))? {
                Outcome::Complete(elaborated) => elaborated,
                Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
            };
        let mut traces = elaborated.traces;
        for trace in &mut traces {
            trace.at = parsed
                .source_view()
                .to_original(fln_parse::BytePos(trace.at))
                .0;
        }
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
}
