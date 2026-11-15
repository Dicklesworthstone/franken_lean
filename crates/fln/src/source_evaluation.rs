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
    /// Raw values and direct stream effects; the caller owns presentation.
    Raw,
    Lean,
    /// Keep supported scalar/list machine values; otherwise select an actual
    /// Repr/ToString printer before admission and execution. The retained
    /// presentation marker distinguishes formatted text from a source String.
    /// Missing printers and resource failures never retry Raw.
    PreferRaw,
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
    /// Compile a checked source function with explicit erased ABI slots.
    SourceValue,
    Evaluation,
}

pub(super) struct ElaboratedEvaluation {
    pub declaration: Declaration,
    pub presentation: Option<EvaluationResultPresentation>,
    /// A private checked predecessor for this evaluation only. Source module
    /// replay must not publish the derived helper or instance declarations.
    pub deriving: Option<DeclarationBatchAdmission>,
}

impl ElaboratedEvaluation {
    fn plain(declaration: Declaration, presentation: Option<EvaluationResultPresentation>) -> Self {
        Self {
            declaration,
            presentation,
            deriving: None,
        }
    }
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
    /// Native output isolated while the source evaluation ran, in write order.
    /// Even an empty Some marks a completed isolation scope. This never reruns IO.
    pub fn evaluation_output(&self) -> Option<&str> {
        self.evaluation_output.as_deref()
    }
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

    /// Ordered stdout and stderr from a pure or IO `#eval`, including native
    /// panic and trace diagnostics, when the `lean` presentation captured it.
    /// Other presentations retain ordinary native writes and return `None`.
    pub fn captured_stdout(&self) -> Option<&[u8]> {
        self.io_stdout.as_deref()
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

pub(super) fn capture_failure<T>(error: fln_rt::obj::StdoutCaptureError) -> Outcome<T> {
    use fln_rt::obj::StdoutCaptureError;
    match error {
        StdoutCaptureError::Limit { limit, requested } => Outcome::Inconclusive(
            fln_core::outcome::Inconclusive::resource(fln_core::outcome::ResourceUsage {
                reason: fln_core::diag::ResourceReason::Memory {
                    limit_bytes: limit as u64,
                },
                allowed: limit as u64,
                observed: requested as u64,
            })
            .with_progress("evaluation output capture byte allowance"),
        ),
        StdoutCaptureError::Allocation => {
            Outcome::Inconclusive(fln_core::outcome::Inconclusive::dependency_unavailable(
                "host allocation for evaluation output capture",
            ))
        }
        StdoutCaptureError::InvalidStdout | StdoutCaptureError::InvalidStderr => {
            Outcome::Inconclusive(fln_core::outcome::Inconclusive::unsupported(
                "evaluation stream is not a supported native stream",
            ))
        }
        StdoutCaptureError::ScopeUnavailable => {
            Outcome::InternalFault(fln_core::outcome::InternalFault::new(
                "EVAL-CAPTURE-SCOPE",
                "evaluation output capture lost its scope",
            ))
        }
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
) -> Result<Outcome<ElaboratedEvaluation>, EngineExecutionError> {
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
                Outcome::Complete(declaration) => {
                    Outcome::Complete(ElaboratedEvaluation::plain(declaration, None))
                }
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
    let mut prepared = match source_records::elaboration_outcome(
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
        return Ok(Outcome::Complete(ElaboratedEvaluation::plain(
            prepared.into_raw(),
            Some(EvaluationResultPresentation::Guard),
        )));
    }
    let mut preparation = runtime::Preparation::new(engine.environment(), limits.ingress);
    let action = preparation
        .evaluation_presentation_type(prepared.type_())
        .map_err(EngineExecutionError::Ingress)?;
    let carrier = action
        .as_ref()
        .map_or_else(|| prepared.type_().clone(), |action| action.value.clone());
    if presentation == EvaluationPresentation::PreferRaw
        && preparation
            .raw_evaluation_result_type(&carrier, action.is_some())
            .map_err(EngineExecutionError::Ingress)?
    {
        return Ok(Outcome::Complete(ElaboratedEvaluation::plain(
            prepared.into_raw(),
            None,
        )));
    }
    let format = |prepared: &mut fln_elab::source::evaluation::PreparedEvaluation| {
        use fln_elab::source::evaluation::PreparedIoEvaluation;
        if let Some(action) = &action {
            prepared
                .io_presentation(action.monad.clone(), action.value.clone())
                .map(|printed| match printed {
                    PreparedIoEvaluation::Unit(declaration) => ElaboratedEvaluation::plain(
                        declaration,
                        Some(EvaluationResultPresentation::IoUnit),
                    ),
                    PreparedIoEvaluation::Format(declaration) => ElaboratedEvaluation::plain(
                        declaration,
                        Some(EvaluationResultPresentation::IoFormat { width: 120 }),
                    ),
                })
        } else {
            prepared.format().map(|declaration| {
                ElaboratedEvaluation::plain(
                    declaration,
                    Some(EvaluationResultPresentation::Format { width: 120 }),
                )
            })
        }
    };
    let missing = match format(&mut prepared) {
        Ok(result) => return Ok(Outcome::Complete(result)),
        Err(error) if missing_printer(&error) => error,
        Err(error) => return source_records::elaboration_outcome(Err(error)),
    };
    let target =
        match source_records::elaboration_outcome(prepared.automatic_deriving_target(&carrier))? {
            Outcome::Complete(Some(target)) => target,
            Outcome::Complete(None) => return source_records::elaboration_outcome(Err(missing)),
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
    let request = fln_elab::source::deriving::ExistingDeriving {
        handlers: vec![Name::from_components(["_root_", "Repr"])],
        targets: vec![target],
        scope: effective_scope,
    };
    // The same generator, kernel/checker admission, instance registration and
    // reducibility path as `deriving instance Repr for T`. Only this temporary
    // successor sees it (`withoutModifyingEnv` in the pin's eval command).
    let deriving = match engine.admit_existing_deriving(
        &request,
        None,
        &request.scope.options,
        limits.admission(),
    ) {
        Ok(Outcome::Complete(deriving)) => deriving,
        Ok(Outcome::Inconclusive(reason)) => return Ok(Outcome::Inconclusive(reason)),
        Ok(Outcome::InternalFault(fault)) => return Ok(Outcome::InternalFault(fault)),
        Err(EngineExecutionError::Frontend(DefinitionFrontendError::Elaborate(
            fln_elab::NatDefinitionElabError::Inference(
                fln_elab::source::SourceInferenceError::Deriving(
                    fln_elab::source::deriving::DerivingError::CannotDeriveRepr(_),
                ),
            ),
        ))) => return source_records::elaboration_outcome(Err(missing)),
        Err(error) => return Err(error),
    };
    match source_records::elaboration_outcome(
        prepared.use_deriving_environment(deriving.engine.environment()),
    )? {
        Outcome::Complete(()) => {}
        Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
        Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
    }
    // At most one deriving attempt. A recursive family uses the existing Repr
    // handler, but missing printers for other field families cannot recurse
    // into another fallback or hide a resource/internal failure.
    source_records::elaboration_outcome(format(&mut prepared).map(|mut result| {
        result.deriving = Some(deriving);
        result
    }))
}

fn missing_printer(error: &fln_elab::NatDefinitionElabError) -> bool {
    matches!(
        error,
        fln_elab::NatDefinitionElabError::Inference(
            fln_elab::source::SourceInferenceError::EvaluationPrinting(
                fln_elab::source::evaluation::PrintingError::MissingPrinter
            )
        )
    )
}

/// `Lean.Parser.Command.guardCmd`, the node `#guard e` parses to.
fn fln_parse_kind_guard() -> Name {
    Name::from_components(["Lean", "Parser", "Command", "guardCmd"])
}
