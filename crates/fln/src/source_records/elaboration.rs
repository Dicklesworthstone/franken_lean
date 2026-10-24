//! Source effects follow successful ordinary admission. They are explicit
//! elaboration results, never guesses from a declaration's name or body.
use super::*;

pub(crate) fn register_irreducible(
    engine: &mut Engine,
    declaration: &Declaration,
) -> Result<(), EngineExecutionError> {
    let Declaration::Defn(definition) = declaration else {
        return Err(EngineExecutionError::UnexpectedPublication {
            detail: "well-founded source lowering must produce a checked definition",
        });
    };
    if !matches!(engine.environment().find(&definition.base.name),
        Some(ConstantInfo::Defn(checked)) if checked == definition)
    {
        return Err(EngineExecutionError::UnexpectedPublication {
            detail: "source effects require the exact admitted definition",
        });
    }
    engine.environment = fln_elab::reducibility::register(
        engine.environment(),
        &definition.base.name,
        fln_elab::reducibility::Reducibility::Irreducible,
    )
    .map_err(|error| {
        EngineExecutionError::Frontend(DefinitionFrontendError::Elaborate(
            fln_elab::NatDefinitionElabError::Inference(
                fln_elab::source::SourceInferenceError::Unification(Box::new(
                    fln_elab::constraint::unify::UnificationError::Reducibility(error),
                )),
            ),
        ))
    })?;
    Ok(())
}

/// Record a definition's equation information (`fln_elab::source::equation_theorems::journal`)
/// with the exact definition it was elaborated with.
pub(crate) fn record_equation_info(
    engine: &mut Engine,
    declaration: &Declaration,
    record: &fln_elab::source::equation_theorems::journal::Record,
) -> Result<(), EngineExecutionError> {
    let Declaration::Defn(definition) = declaration else {
        return Err(EngineExecutionError::UnexpectedPublication {
            detail: "equation information requires a checked definition",
        });
    };
    if definition.base.name != record.declaration
        || !matches!(engine.environment().find(&definition.base.name),
            Some(ConstantInfo::Defn(checked)) if checked == definition)
    {
        return Err(EngineExecutionError::UnexpectedPublication {
            detail: "equation information requires the exact admitted definition",
        });
    }
    engine.environment =
        fln_elab::source::equation_theorems::journal::push(engine.environment(), record).map_err(
            |error| EngineExecutionError::Frontend(DefinitionFrontendError::Elaborate(error)),
        )?;
    Ok(())
}

pub(crate) fn apply_admission_effects(
    admission: &mut DeclarationAdmission,
    irreducible: bool,
    equations: Option<&fln_elab::source::equation_theorems::journal::Record>,
    options: &KVMap,
) -> Result<(), EngineExecutionError> {
    if irreducible {
        register_irreducible(&mut admission.engine, &admission.declaration)?;
        admission.result_logical_root = admission.engine.logical_root(options);
    }
    if let Some(record) = equations {
        record_equation_info(&mut admission.engine, &admission.declaration, record)?;
        admission.result_logical_root = admission.engine.logical_root(options);
    }
    Ok(())
}

pub(crate) fn apply_batch_effects(
    batch: &mut DeclarationBatchAdmission,
    irreducible: bool,
    equations: Option<&fln_elab::source::equation_theorems::journal::Record>,
    options: &KVMap,
) -> Result<(), EngineExecutionError> {
    if irreducible || equations.is_some() {
        let [admission] = batch.admissions.as_mut_slice() else {
            return Err(EngineExecutionError::UnexpectedPublication {
                detail: "a source definition effect requires one admitted declaration",
            });
        };
        apply_admission_effects(admission, irreducible, equations, options)?;
        batch.engine = admission.engine.clone();
        batch.result_logical_root = admission.result_logical_root;
    }
    Ok(())
}

pub(crate) fn apply_execution_effects(
    execution: &mut DefinitionExecution,
    irreducible: bool,
    equations: Option<&fln_elab::source::equation_theorems::journal::Record>,
    options: &KVMap,
) -> Result<(), EngineExecutionError> {
    if irreducible {
        register_irreducible(&mut execution.engine, &execution.declaration)?;
        execution.result_logical_root = execution.engine.logical_root(options);
    }
    if let Some(record) = equations {
        record_equation_info(&mut execution.engine, &execution.declaration, record)?;
        execution.result_logical_root = execution.engine.logical_root(options);
    }
    Ok(())
}
