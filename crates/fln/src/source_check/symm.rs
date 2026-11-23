//! Transactional symmetry attributes, shared by checking and executing source.
//! Imported declarations may be tagged; local selection never enters an export.
use super::*;
use fln_elab::source::scope::{SourceScope, executable, symm};
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
    scope: &mut SourceScope,
    syntax: &Syntax,
    limits: EngineAdmissionLimits,
    position: (usize, usize, usize),
) -> Result<Outcome<Vec<DeclarationAdmission>>, SourceCheckError> {
    let (kinds, names) = match elaborate(symm::command(syntax), position)? {
        Outcome::Complete(request) => request,
        Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
        Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
    };
    let mut next = engine.environment.clone();
    let mut next_scope = scope.clone();
    for requested in names {
        let name = match elaborate(resolve(&next, &next_scope, &requested), position)? {
            Outcome::Complete(name) => name,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        let lemma = match elaborate(
            symm::compile(&next, &next_scope, &name, limits.kernel),
            position,
        )? {
            Outcome::Complete(lemma) => lemma,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        next = match elaborate(
            symm::apply(&next, &mut next_scope, &lemma, &kinds),
            position,
        )? {
            Outcome::Complete(next) => next,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
    }
    engine.environment = next;
    scope.symm_scopes = next_scope.symm_scopes;
    Ok(Outcome::Complete(Vec::new()))
}

pub(super) fn apply_module(
    engine: &mut Engine,
    scopes: &mut scopes::Scopes,
    syntax: &Syntax,
    limits: EngineAdmissionLimits,
    position: (usize, usize, usize),
    public: Option<&mut modules::visibility::PublicWorld<'_>>,
) -> Result<Outcome<Vec<DeclarationAdmission>>, SourceCheckError> {
    let Some(public) = public else {
        return apply_private(engine, &mut scopes.current, syntax, limits, position);
    };
    let (kinds, names) = match elaborate(symm::command(syntax), position)? {
        Outcome::Complete(request) => request,
        Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
        Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
    };
    let mut private_env = engine.environment.clone();
    let mut public_env = public.engine().environment().clone();
    let mut private_scope = scopes.current.clone();
    let mut public_scope = scopes.public_scope();
    for requested in names {
        let name = match elaborate(resolve(&private_env, &private_scope, &requested), position)? {
            Outcome::Complete(name) => name,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        let lemma = match elaborate(
            symm::compile(&private_env, &private_scope, &name, limits.kernel),
            position,
        )? {
            Outcome::Complete(lemma) => lemma,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        private_env = match elaborate(
            symm::apply(&private_env, &mut private_scope, &lemma, &kinds),
            position,
        )? {
            Outcome::Complete(next) => next,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        if public_env.contains(&name) {
            public_env = match elaborate(
                symm::apply(&public_env, &mut public_scope, &lemma, &kinds),
                position,
            )? {
                Outcome::Complete(next) => next,
                Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
            };
        }
    }
    let next = match public
        .publish_symm_attributes(engine, private_env, public_env)
        .map_err(|error| frontend(position, error))?
    {
        Outcome::Complete(next) => next,
        Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
        Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
    };
    *engine = next;
    scopes.set_symm_scopes(private_scope.symm_scopes, public_scope.symm_scopes);
    Ok(Outcome::Complete(Vec::new()))
}
