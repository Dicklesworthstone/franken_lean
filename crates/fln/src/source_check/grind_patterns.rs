//! Register explicit triggers atomically in private and exported source views.
//! Patterns are compiled once in the proof's telescope, before publication.
use super::*;
use fln_elab::grind_patterns as registry;
use fln_elab::source::grind_patterns as source_patterns;
use fln_elab::source::scope::SourceScope;
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

fn compile(
    env: &Environment,
    scope: &SourceScope,
    syntax: &Syntax,
    limits: EngineAdmissionLimits,
) -> Result<registry::GrindPattern, fln_elab::NatDefinitionElabError> {
    let request = source_patterns::command(syntax)?;
    source_patterns::compile(env, scope, limits.kernel, &request)
}

pub(super) fn apply_private(
    engine: &mut Engine,
    scope: &SourceScope,
    syntax: &Syntax,
    limits: EngineAdmissionLimits,
    position: (usize, usize, usize),
) -> Result<Outcome<Vec<DeclarationAdmission>>, SourceCheckError> {
    let row = match elaborate(
        compile(engine.environment(), scope, syntax, limits),
        position,
    )? {
        Outcome::Complete(row) => row,
        Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
        Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
    };
    let next = match elaborate(
        registry::register(engine.environment(), &[row]).map_err(source_patterns::registry_error),
        position,
    )? {
        Outcome::Complete(next) => next,
        Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
        Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
    };
    engine.environment = next;
    Ok(Outcome::Complete(Vec::new()))
}

pub(super) fn apply_module(
    engine: &mut Engine,
    scopes: &scopes::Scopes,
    syntax: &Syntax,
    limits: EngineAdmissionLimits,
    position: (usize, usize, usize),
    public: Option<&mut modules::visibility::PublicWorld<'_>>,
) -> Result<Outcome<Vec<DeclarationAdmission>>, SourceCheckError> {
    let Some(public) = public else {
        return apply_private(engine, &scopes.current, syntax, limits, position);
    };
    let row = match elaborate(
        compile(engine.environment(), &scopes.current, syntax, limits),
        position,
    )? {
        Outcome::Complete(row) => row,
        Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
        Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
    };
    let private_env = match elaborate(
        registry::register(engine.environment(), std::slice::from_ref(&row))
            .map_err(source_patterns::registry_error),
        position,
    )? {
        Outcome::Complete(next) => next,
        Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
        Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
    };
    let public_env = if public.engine().environment().contains(&row.declaration) {
        // The public registry independently validates every pattern dependency;
        // a private symbol in a public proof's trigger cannot escape this world.
        match elaborate(
            registry::register(public.engine().environment(), &[row])
                .map_err(source_patterns::registry_error),
            position,
        )? {
            Outcome::Complete(next) => next,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        }
    } else {
        public.engine().environment().clone()
    };
    match public
        .publish_grind_patterns(engine, private_env, public_env)
        .map_err(|error| frontend(position, error))?
    {
        Outcome::Complete(next) => {
            *engine = next;
            Ok(Outcome::Complete(Vec::new()))
        }
        Outcome::Inconclusive(reason) => Ok(Outcome::Inconclusive(reason)),
        Outcome::InternalFault(fault) => Ok(Outcome::InternalFault(fault)),
    }
}
