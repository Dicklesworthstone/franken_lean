//! Source declarations may own lifted helpers. Retain each council receipt and
//! root transition; never claim the owner's checker admitted its helpers.
use super::*;

/// One source declaration and all of its separately checked local helpers.
/// `checker` describes the primary declaration only. `admissions` carries every
/// actual transition, in publication order, including the primary at index 0.
#[derive(Debug)]
pub struct SourceDeclarationAdmission {
    pub engine: Engine,
    pub declaration: Declaration,
    pub base_logical_root: LogicalRoot,
    pub result_logical_root: LogicalRoot,
    pub checker: CheckerAgreement,
    pub admissions: Vec<DeclarationAdmission>,
}
impl SourceDeclarationAdmission {
    pub fn into_batch(self) -> DeclarationBatchAdmission {
        DeclarationBatchAdmission {
            engine: self.engine,
            base_logical_root: self.base_logical_root,
            result_logical_root: self.result_logical_root,
            admissions: self.admissions,
            local_instance: None,
        }
    }
}

impl Engine {
    pub(crate) fn finish_local_function_batch(
        &self,
        mut batch: DeclarationBatchAdmission,
        helpers: &[Declaration],
        options: &KVMap,
        limits: EngineAdmissionLimits,
    ) -> Result<Outcome<DeclarationBatchAdmission>, EngineExecutionError> {
        if helpers.is_empty() {
            return Ok(Outcome::Complete(batch));
        }
        let owner =
            batch
                .admissions
                .first()
                .ok_or(EngineExecutionError::UnexpectedPublication {
                    detail: "local helpers require a checked owner",
                })?;
        let owner_name = match &owner.declaration {
            Declaration::Defn(value) => &value.base.name,
            Declaration::Thm(value) => &value.base.name,
            Declaration::Opaque(value) => &value.base.name,
            Declaration::Axiom(value) => &value.base.name,
            _ => {
                return Err(EngineExecutionError::UnexpectedPublication {
                    detail: "local helper owner is not a named declaration",
                });
            }
        };
        let noncomputable = fln_elab::noncomputable::read(batch.engine.environment())
            .map_err(|error| {
                EngineExecutionError::Frontend(DefinitionFrontendError::Elaborate(
                    fln_elab::NatDefinitionElabError::Inference(
                        fln_elab::source::SourceInferenceError::NoncomputableJournal(error),
                    ),
                ))
            })?
            .contains(owner_name);
        for helper in helpers {
            let mut admitted =
                match batch
                    .engine
                    .admit_declaration(helper.clone(), options, limits)?
                {
                    Outcome::Complete(value) => value,
                    Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                    Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
                };
            if noncomputable {
                admitted.engine.environment = tag_noncomputable(
                    &admitted.engine,
                    &admitted.declaration,
                    &Name::anonymous(),
                    &fln_elab::source::scope::SourceScope::default(),
                )?;
                admitted.result_logical_root = admitted.engine.logical_root(options);
            }
            batch.engine = admitted.engine.clone();
            batch.admissions.push(admitted);
        }
        batch.result_logical_root = batch.engine.logical_root(options);
        Ok(Outcome::Complete(batch))
    }

    pub(crate) fn finish_local_function_admission(
        &self,
        primary: DeclarationAdmission,
        helpers: &[Declaration],
        options: &KVMap,
        limits: EngineAdmissionLimits,
    ) -> Result<Outcome<SourceDeclarationAdmission>, EngineExecutionError> {
        let declaration = primary.declaration.clone();
        let checker = primary.checker;
        let batch = DeclarationBatchAdmission {
            engine: primary.engine.clone(),
            base_logical_root: primary.base_logical_root,
            result_logical_root: primary.result_logical_root,
            admissions: vec![primary],
            local_instance: None,
        };
        Ok(self
            .finish_local_function_batch(batch, helpers, options, limits)?
            .map_complete(|batch| SourceDeclarationAdmission {
                engine: batch.engine,
                declaration,
                checker,
                base_logical_root: batch.base_logical_root,
                result_logical_root: batch.result_logical_root,
                admissions: batch.admissions,
            }))
    }
}
