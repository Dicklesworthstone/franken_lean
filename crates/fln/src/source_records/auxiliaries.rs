//! Publish the pin's derived recursor wrappers with their inductive command.
//! Candidate generation has no admission authority: the original family and
//! every generated definition still pass both checking seats, in order.
use super::*;
use fln_elab::inductive::auxiliaries::{cases_on_declaration, rec_on_declaration};
use fln_elab::source::SourceInferenceError;

fn frontend(reason: SourceInferenceError) -> EngineExecutionError {
    EngineExecutionError::Frontend(DefinitionFrontendError::Elaborate(
        fln_elab::NatDefinitionElabError::Inference(reason),
    ))
}

impl Engine {
    pub(super) fn finish_source_inductive_auxiliaries(
        &self,
        result: Outcome<DeclarationBatchAdmission>,
        options: &KVMap,
        limits: EngineAdmissionLimits,
    ) -> Result<Outcome<DeclarationBatchAdmission>, EngineExecutionError> {
        let mut batch = match result {
            Outcome::Complete(batch) => batch,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        let mut candidates = Vec::new();
        let mut protected = Vec::new();
        // mkAuxConstructions tests PUnit once after admitting the inductive
        // block. A prelude-free bootstrap can therefore generate recOn before
        // PUnit exists, just as the pin does.
        let has_unit = batch
            .engine
            .environment()
            .contains(&Name::from_components(["PUnit"]));
        let budget = fln_elab::records::RecordBudget::default();
        for admission in &batch.admissions {
            let Declaration::Inductive(block) = &admission.declaration else {
                continue;
            };
            for inductive in &block.types {
                let recursor_name = Name::str(inductive.base.name.clone(), "rec");
                let Some(ConstantInfo::Rec(recursor)) =
                    batch.engine.environment().find(&recursor_name)
                else {
                    return Err(EngineExecutionError::UnexpectedPublication {
                        detail: "an admitted source inductive has no checked recursor",
                    });
                };
                let rec_on = rec_on_declaration(recursor, budget)
                    .map_err(|error| frontend(SourceInferenceError::Auxiliary(error)))?;
                protected.push(rec_on.base.name.clone());
                candidates.push(Declaration::Defn(rec_on));
                if has_unit {
                    let cases_on = cases_on_declaration(inductive, recursor, &block.types, budget)
                        .map_err(|error| frontend(SourceInferenceError::Auxiliary(error)))?;
                    candidates.push(Declaration::Defn(cases_on));
                }
            }
        }
        if candidates.is_empty() {
            return Ok(Outcome::Complete(batch));
        }
        let names: Vec<_> = candidates
            .iter()
            .filter_map(|candidate| match candidate {
                Declaration::Defn(definition) => Some(definition.base.name.clone()),
                _ => None,
            })
            .collect();
        let mut successor = match batch
            .engine
            .admit_declarations(&candidates, options, limits)
            .map_err(EngineExecutionError::from)?
        {
            Outcome::Complete(successor) => successor,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        for name in &names {
            successor.engine.environment = fln_elab::reducibility::register(
                successor.engine.environment(),
                name,
                fln_elab::reducibility::Reducibility::Reducible,
            )
            .map_err(|error| {
                frontend(SourceInferenceError::Unification(Box::new(
                    fln_elab::constraint::unify::UnificationError::Reducibility(error),
                )))
            })?;
        }
        successor.engine.environment =
            fln_elab::aux_recursors::register_module(successor.engine.environment(), &names)
                .map_err(|error| frontend(SourceInferenceError::AuxiliaryJournal(error)))?;
        successor.engine.environment =
            fln_elab::protected_names::register_module(successor.engine.environment(), &protected)
                .map_err(|error| frontend(SourceInferenceError::ProtectedJournal(error)))?;
        // Keep every council receipt in the command's admission stream so
        // module export and replay carry the actual generated definitions.
        // A late collision, budget stop, or journal error exposes no prefix.
        batch.admissions.extend(successor.admissions);
        batch.engine = successor.engine;
        batch.result_logical_root = batch.engine.logical_root(options);
        Ok(Outcome::Complete(batch))
    }
}
