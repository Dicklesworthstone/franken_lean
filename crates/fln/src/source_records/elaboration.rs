//! Source effects follow successful ordinary admission. They are explicit
//! elaboration results, never guesses from a declaration's name or body.
use super::*;

fn has_source_reducibility(declaration: &Declaration, is_instance: bool) -> bool {
    matches!(declaration, Declaration::Defn(definition)
        if definition.hints == fln_env::constants::ReducibilityHints::Abbrev
            || (!is_instance && definition.safety != DefinitionSafety::Partial))
}

/// Record the checked source declaration's default before explicit attributes.
/// Source elaboration emits Abbrev hints only for an abbreviation; ordinary
/// definitions start semireducible. Data instances retain their separate
/// implicit-reducibility effect instead of acquiring an ordinary default.
/// An imported definition's hints alone must not authorize a consumer to infer
/// either status.
fn register_source_reducibility(
    engine: &mut Engine,
    declaration: &Declaration,
    is_instance: bool,
) -> Result<bool, EngineExecutionError> {
    if !has_source_reducibility(declaration, is_instance) {
        return Ok(false);
    }
    let Declaration::Defn(definition) = declaration else {
        unreachable!("source definition effects require a definition")
    };
    if !matches!(engine.environment().find(&definition.base.name),
        Some(ConstantInfo::Defn(checked)) if checked == definition)
    {
        return Err(EngineExecutionError::UnexpectedPublication {
            detail: "source reducibility effects require the exact admitted definition",
        });
    }
    let status = if definition.hints == fln_env::constants::ReducibilityHints::Abbrev {
        fln_elab::reducibility::Reducibility::Reducible
    } else {
        fln_elab::reducibility::Reducibility::Semireducible
    };
    engine.environment = set_reducibility(engine, &definition.base.name, status)?;
    Ok(true)
}

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
    is_instance: bool,
    irreducible: bool,
    equations: Option<&fln_elab::source::equation_theorems::journal::Record>,
    options: &KVMap,
) -> Result<(), EngineExecutionError> {
    if register_source_reducibility(&mut admission.engine, &admission.declaration, is_instance)? {
        admission.result_logical_root = admission.engine.logical_root(options);
    }
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
    is_instance: bool,
    irreducible: bool,
    equations: Option<&fln_elab::source::equation_theorems::journal::Record>,
    options: &KVMap,
) -> Result<(), EngineExecutionError> {
    if irreducible
        || equations.is_some()
        || batch
            .admissions
            .iter()
            .any(|admission| has_source_reducibility(&admission.declaration, is_instance))
    {
        let [admission] = batch.admissions.as_mut_slice() else {
            return Err(EngineExecutionError::UnexpectedPublication {
                detail: "a source definition effect requires one admitted declaration",
            });
        };
        apply_admission_effects(admission, is_instance, irreducible, equations, options)?;
        batch.engine = admission.engine.clone();
        batch.result_logical_root = admission.result_logical_root;
    }
    Ok(())
}

pub(crate) fn apply_execution_effects(
    execution: &mut DefinitionExecution,
    is_instance: bool,
    irreducible: bool,
    equations: Option<&fln_elab::source::equation_theorems::journal::Record>,
    options: &KVMap,
) -> Result<(), EngineExecutionError> {
    if register_source_reducibility(&mut execution.engine, &execution.declaration, is_instance)? {
        execution.result_logical_root = execution.engine.logical_root(options);
    }
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
