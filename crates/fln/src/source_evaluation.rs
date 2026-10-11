//! Explicit source evaluation intent and typed IO results.
//!
//! The command adapter, not a value's runtime tag, requests IO execution. The
//! selected declaration, including any requested printer map, passes ordinary
//! checking before its action is applied to the runtime-owned ST token inside
//! the retained FIR/FLBC program.

use super::*;

/// Whether source evaluations retain their raw values or explicitly request
/// the supported Lean presentation through actual class instances.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EvaluationPresentation {
    Raw,
    Lean,
}

/// Presentation selected by the source adapter before ordinary admission and
/// execution. Familiar type names or runtime tags never create this marker.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EvaluationResultPresentation {
    /// The complete VM result is a checked `Std.Format` value.
    Format { width: usize },
    /// The checked IO action maps its successful payload to `Std.Format`.
    /// Its exception result remains an exception and has no printable Format.
    IoFormat { width: usize },
    /// The checked action's payload is definitionally Unit. Success is silent;
    /// the ordinary typed IO projection must still validate it or its exception.
    IoUnit,
    /// `#guard e`: the checked result is a `Bool`. `true` is silent; `false` refuses the command
    /// (`evalGuardCmd`, Lean/Elab/Tactic/Guard.lean).
    Guard,
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
    /// IO results use `evaluation_presentation` and typed payload projection.
    pub fn evaluation_format_width(&self) -> Option<usize> {
        match self.evaluation_presentation {
            Some(EvaluationResultPresentation::Format { width }) => Some(width),
            _ => None,
        }
    }

    /// The explicit checked presentation of a source evaluation, if selected.
    /// This does not execute an action or project its runtime representation.
    pub fn evaluation_presentation(&self) -> Option<EvaluationResultPresentation> {
        self.evaluation_presentation
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
) -> Result<Outcome<(Declaration, Option<EvaluationResultPresentation>)>, EngineExecutionError> {
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
    // Classification also retains a canonical monad for Functor.map rather
    // than letting an exposed world arrow infer a Reader instance. It validates
    // the original aliases before mapping can change their type spelling.
    if syntax.kind() == Some(&fln_parse_kind_guard()) {
        return Ok(Outcome::Complete((
            prepared.into_raw(),
            Some(EvaluationResultPresentation::Guard),
        )));
    }
    let mut preparation = runtime::Preparation::new(engine.environment(), limits.ingress);
    if let Some(action) = preparation
        .evaluation_presentation_type(prepared.type_())
        .map_err(EngineExecutionError::Ingress)?
    {
        use fln_elab::source::evaluation::PreparedIoEvaluation;
        return Ok(
            match source_records::elaboration_outcome(
                prepared.into_io_presentation(action.monad, action.value),
            )? {
                Outcome::Complete(PreparedIoEvaluation::Unit(declaration)) => {
                    Outcome::Complete((declaration, Some(EvaluationResultPresentation::IoUnit)))
                }
                Outcome::Complete(PreparedIoEvaluation::Format(declaration)) => {
                    Outcome::Complete((
                        declaration,
                        Some(EvaluationResultPresentation::IoFormat { width: 120 }),
                    ))
                }
                Outcome::Inconclusive(reason) => Outcome::Inconclusive(reason),
                Outcome::InternalFault(fault) => Outcome::InternalFault(fault),
            },
        );
    }
    Ok(
        match source_records::elaboration_outcome(prepared.into_format())? {
            Outcome::Complete(declaration) => Outcome::Complete((
                declaration,
                Some(EvaluationResultPresentation::Format { width: 120 }),
            )),
            Outcome::Inconclusive(reason) => Outcome::Inconclusive(reason),
            Outcome::InternalFault(fault) => Outcome::InternalFault(fault),
        },
    )
}

/// `Lean.Parser.Command.guardCmd`, the node `#guard e` parses to.
fn fln_parse_kind_guard() -> Name {
    Name::from_components(["Lean", "Parser", "Command", "guardCmd"])
}
