//! Late constructor auxiliaries follow the same checked admission and public
//! replay path as source declarations. A failed target publishes no prefix.
use super::*;
use fln_elab::source::scope::{SourceScope, constructor_elims, executable};
use fln_syntax::tree::Syntax;

fn frontend(position: (usize, usize, usize), error: EngineExecutionError) -> SourceCheckError {
    command_error(
        position.0,
        position.1,
        fln_parse::BytePos(position.2),
        error,
    )
}

fn elaborate<T>(
    value: Result<T, fln_elab::NatDefinitionElabError>,
    position: (usize, usize, usize),
) -> Result<Outcome<T>, SourceCheckError> {
    source_records::elaboration_outcome(value).map_err(|error| frontend(position, error))
}

fn resolve(
    env: &Environment,
    scope: &SourceScope,
    requested: &Name,
) -> Result<Name, fln_elab::NatDefinitionElabError> {
    executable::resolve(env, scope, requested)?.ok_or_else(|| {
        fln_elab::NatDefinitionElabError::Inference(
            fln_elab::source::SourceInferenceError::UnknownConstant(requested.clone()),
        )
    })
}

pub(super) fn apply_private(
    engine: &mut Engine,
    scope: &SourceScope,
    syntax: &Syntax,
    limits: EngineAdmissionLimits,
    position: (usize, usize, usize),
    options: &KVMap,
) -> Result<Outcome<Vec<DeclarationAdmission>>, SourceCheckError> {
    let (repetitions, names) = match elaborate(constructor_elims::command(syntax), position)? {
        Outcome::Complete(request) => request,
        Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
        Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
    };
    let mut next = engine.clone();
    let mut admissions = Vec::new();
    for requested in names {
        let name = match elaborate(resolve(next.environment(), scope, &requested), position)? {
            Outcome::Complete(name) => name,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        for _ in 0..repetitions {
            let generated = match next
                .generate_source_constructor_elims(&name, options, limits, scope)
                .map_err(|error| frontend(position, error))?
            {
                Outcome::Complete(generated) => generated,
                Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
            };
            next = generated.engine;
            admissions.extend(generated.admissions);
        }
    }
    *engine = next;
    Ok(Outcome::Complete(admissions))
}

#[allow(clippy::too_many_arguments)]
pub(super) fn apply_module(
    engine: &mut Engine,
    scopes: &scopes::Scopes,
    syntax: &Syntax,
    limits: EngineAdmissionLimits,
    position: (usize, usize, usize),
    options: &KVMap,
    public: Option<&mut modules::visibility::PublicWorld<'_>>,
) -> Result<Outcome<Vec<DeclarationAdmission>>, SourceCheckError> {
    let Some(public) = public else {
        return apply_private(engine, &scopes.current, syntax, limits, position, options);
    };
    let (repetitions, names) = match elaborate(constructor_elims::command(syntax), position)? {
        Outcome::Complete(request) => request,
        Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
        Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
    };
    let mut private_next = engine.clone();
    let mut public_next = public.engine().clone();
    let public_base = public_next.logical_root(options);
    let public_scope = scopes.public_scope();
    let mut public_declarations = Vec::new();
    let mut admissions = Vec::new();
    for requested in names {
        let name = match elaborate(
            resolve(private_next.environment(), &scopes.current, &requested),
            position,
        )? {
            Outcome::Complete(name) => name,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        // mkCtorIdx/mkCtorElim use withExporting for a public target. Its
        // auxiliaries may therefore depend only on the public checked world.
        // Private targets retain their mangled owner and private dependencies.
        let public_owner = public_next.environment().contains(&name);
        for _ in 0..repetitions {
            let (target, scope) = if public_owner {
                (&public_next, &public_scope)
            } else {
                (&private_next, &scopes.current)
            };
            let generated = match target
                .generate_source_constructor_elims(&name, options, limits, scope)
                .map_err(|error| frontend(position, error))?
            {
                Outcome::Complete(generated) => generated,
                Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
            };
            if public_owner {
                public_declarations.extend(
                    generated
                        .admissions
                        .iter()
                        .map(|admission| admission.declaration.clone()),
                );
                public_next = generated.engine;
            } else {
                private_next = generated.engine;
            }
            admissions.extend(generated.admissions);
        }
    }
    if public_next.logical_root(options) != public_base {
        private_next = match public
            .publish(
                &private_next,
                public_next,
                public_declarations,
                &public_scope,
                options,
            )
            .map_err(|error| frontend(position, error))?
        {
            Outcome::Complete(next) => next,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
    }
    *engine = private_next;
    Ok(Outcome::Complete(admissions))
}
