//! One source command may expand to multiple mutually dependent declarations.
//! Preserve the ordinary per-declaration evidence and publish only a full batch.
use super::*;

impl Engine {
    /// Admit one definition, theorem, instance, structure or class command.
    /// A record's block and projections all pass K1 and the independent checker
    /// before class metadata is registered. No failed prefix is exposed.
    pub fn admit_source_command(
        &self,
        source: &[u8],
        options: &KVMap,
        limits: EngineAdmissionLimits,
    ) -> Result<Outcome<DeclarationBatchAdmission>, EngineExecutionError> {
        let parsed = fln_parse::parse_definition(source)
            .map_err(DefinitionFrontendError::Parse)
            .map_err(EngineExecutionError::Frontend)?;
        if !fln_elab::source::is_record(parsed.syntax()) {
            return Ok(
                match self.admit_source_declaration(source, options, limits)? {
                    Outcome::Complete(admitted) => Outcome::Complete(DeclarationBatchAdmission {
                        engine: admitted.engine.clone(),
                        base_logical_root: admitted.base_logical_root,
                        result_logical_root: admitted.result_logical_root,
                        admissions: vec![admitted],
                    }),
                    Outcome::Inconclusive(reason) => Outcome::Inconclusive(reason),
                    Outcome::InternalFault(fault) => Outcome::InternalFault(fault),
                },
            );
        }
        let record = fln_elab::source::elaborate_record(
            parsed.syntax(),
            self.environment(),
            limits.kernel,
            fln_elab::records::RecordBudget::default(),
        )
        .map_err(DefinitionFrontendError::Elaborate)
        .map_err(EngineExecutionError::Frontend)?;
        let result = self
            .admit_declarations(&record.declarations, options, limits)
            .map_err(EngineExecutionError::from)?;
        Ok(match result {
            Outcome::Complete(mut batch) => {
                if record.is_class {
                    batch.engine.environment = fln_elab::instances::register_class(
                        batch.engine.environment(),
                        &record.name,
                    )
                    .map_err(|error| {
                        EngineExecutionError::Frontend(DefinitionFrontendError::Elaborate(
                            fln_elab::NatDefinitionElabError::Inference(
                                fln_elab::source::SourceInferenceError::InstanceRegistry(error),
                            ),
                        ))
                    })?;
                    batch.result_logical_root = batch.engine.logical_root(options);
                }
                Outcome::Complete(batch)
            }
            Outcome::Inconclusive(reason) => Outcome::Inconclusive(reason),
            Outcome::InternalFault(fault) => Outcome::InternalFault(fault),
        })
    }
}
