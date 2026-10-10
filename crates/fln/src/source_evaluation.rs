//! Explicit source evaluation intent and typed IO results.
//!
//! The command adapter, not a value's runtime tag, requests IO execution. The
//! original declaration is checked unchanged; its selected action is applied
//! to the runtime-owned ST token inside the retained FIR/FLBC program.

use super::*;

/// Whether source evaluations retain their raw values or explicitly request
/// the supported Lean presentation through actual class instances.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EvaluationPresentation {
    Raw,
    Lean,
}

#[derive(Clone, Copy)]
pub(super) enum Entry {
    Value,
    Evaluation,
}

#[derive(Debug)]
pub(super) struct IoResultTypes {
    pub value: Expr,
    pub error: Option<Expr>,
}

/// The result of an explicitly evaluated, checked IO or BaseIO action.
///
/// Each payload retains its normalized checked type and the original VM usage.
/// The execution's own exit and bytecode still contain the complete logical
/// ST/EST result, including its runtime world slot. An exception is a separate
/// result, never a successful scalar or a VM panic.
#[derive(Debug)]
pub enum IoEvaluationOutcome {
    Returned { runtime_type: Expr, exit: VmExit },
    Raised { runtime_type: Expr, exit: VmExit },
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum IoEvaluationProjectionError {
    NonReturningExit,
    InvalidResultRepresentation,
}

impl fmt::Display for IoEvaluationProjectionError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
            Self::NonReturningExit => "IO evaluation did not return a VM value",
            Self::InvalidResultRepresentation => {
                "IO evaluation returned a malformed logical ST/EST result"
            }
        })
    }
}

impl std::error::Error for IoEvaluationProjectionError {}

impl DefinitionExecution {
    /// The supported message width when this execution is a checked Repr or
    /// ToString printer result. The VM result is `Std.Format`; ordinary values
    /// of that type and raw Strings never acquire this presentation marker.
    pub fn evaluation_format_width(&self) -> Option<usize> {
        self.evaluation_format_width
    }

    /// Read the typed result of explicit `#eval` IO execution. Ordinary
    /// definitions and pure evaluations return `None`; this never runs a
    /// deferred action or changes the retained environment.
    pub fn io_evaluation_outcome(
        &self,
    ) -> Result<Option<IoEvaluationOutcome>, IoEvaluationProjectionError> {
        let Some(types) = &self.io_result_types else {
            return Ok(None);
        };
        let VmExit::Returned(returned) = &self.exit else {
            return Err(IoEvaluationProjectionError::NonReturningExit);
        };
        let invalid = IoEvaluationProjectionError::InvalidResultRepresentation;
        let result = &returned.value;
        if result.is_scalar() || result.header().other != 2 {
            return Err(invalid);
        }
        let tag = result.header().tag;
        let runtime_type = match (tag, types.error.as_ref()) {
            (0, _) => &types.value,
            (1, Some(error)) => error,
            _ => return Err(invalid),
        };
        let world = result.try_ctor_child(1).ok_or(invalid)?;
        if !world.is_scalar() || world.unbox() != 0 {
            return Err(invalid);
        }
        let value = result.try_ctor_child(0).ok_or(invalid)?;
        let exit = VmExit::Returned(fln_vm::interpreter::CompletedExecution {
            value,
            usage: returned.usage,
        });
        Ok(Some(if tag == 0 {
            IoEvaluationOutcome::Returned {
                runtime_type: runtime_type.clone(),
                exit,
            }
        } else {
            IoEvaluationOutcome::Raised {
                runtime_type: runtime_type.clone(),
                exit,
            }
        }))
    }
}

pub(super) fn elaborate(
    engine: &Engine,
    syntax: &fln_syntax::tree::Syntax,
    name: Name,
    scope: &fln_elab::source::scope::SourceScope,
    options: &KVMap,
    limits: EngineExecutionLimits,
    presentation: EvaluationPresentation,
) -> Result<Outcome<(Declaration, Option<usize>)>, EngineExecutionError> {
    if presentation == EvaluationPresentation::Raw {
        return Ok(
            match source_records::elaboration_outcome(
                fln_elab::elaborate_evaluation_in_scope_with_budget(
                    syntax,
                    name,
                    engine.environment(),
                    limits.kernel,
                    scope,
                ),
            )? {
                Outcome::Complete(declaration) => Outcome::Complete((declaration, None)),
                Outcome::Inconclusive(reason) => Outcome::Inconclusive(reason),
                Outcome::InternalFault(fault) => Outcome::InternalFault(fault),
            },
        );
    }
    let mut effective_scope = scope.clone();
    effective_scope.options = options.clone();
    for (name, value) in scope.options.entries() {
        effective_scope.options.insert(name.clone(), value.clone());
    }
    let prepared = match source_records::elaboration_outcome(
        fln_elab::source::evaluation::PreparedEvaluation::new(
            syntax,
            name,
            engine.environment(),
            limits.kernel,
            &effective_scope,
        ),
    )? {
        Outcome::Complete(prepared) => prepared,
        Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
        Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
    };
    // This is the same metered logical type classifier as the existing IO
    // entry adapter, including safe aliases and exposed world-token arrows.
    // Classification never executes an action or grants its runtime contract.
    let mut preparation = runtime::Preparation::new(engine.environment(), limits.ingress);
    if preparation
        .is_evaluation_action(prepared.type_())
        .map_err(EngineExecutionError::Ingress)?
    {
        return Ok(Outcome::Complete((prepared.into_raw(), None)));
    }
    Ok(
        match source_records::elaboration_outcome(prepared.into_format())? {
            Outcome::Complete(declaration) => Outcome::Complete((declaration, Some(120))),
            Outcome::Inconclusive(reason) => Outcome::Inconclusive(reason),
            Outcome::InternalFault(fault) => Outcome::InternalFault(fault),
        },
    )
}
