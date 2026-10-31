//! Imported node macros on source declarations, standalone `#check` and raw `#eval`.
//!
//! This is an explicit embedding door for syntax the current parser already
//! understands. It installs no artifact parser descriptions. The prepared
//! registry owns the expansion pass: no template expansion runs before it or
//! replays its results. The resulting native Syntax enters the same elaborator
//! and dual-check admission as `Engine::check_source_command`; raw evaluations
//! then use the ordinary compiler, codec and Golem execution path.
//!
//! Recursive expansion follows `Lean.expandMacros`, including its tactic
//! boundary. Atomic macro dispatch belongs to term elaboration, which this
//! bounded adapter does not replace. A surviving identifier, atom or missing
//! node with an active registration is therefore refused explicitly, as is a
//! registered macro left behind the tactic-evaluator boundary.

use super::lookup::EnvironmentMacroLookup;
use super::registrations::{
    MacroAttempt, MacroDispatchInvocation, MacroRegistrationError, MacroTreeLimits,
    MacroTreeResult, RegisteredMacros,
};
use super::{MacroContext, MacroExecutionError, MacroState};
use crate::{
    DefinitionExecution, Engine, EngineAdmissionLimits, EngineExecutionError,
    EngineExecutionLimits, SourceCheck, SourceDeclarationAdmission,
};
use fln_core::diag::ResourceReason;
use fln_core::name::Name;
use fln_core::options::KVMap;
use fln_core::outcome::{Inconclusive, Outcome, ResourceUsage};
use fln_parse::{ParsedSourceCommand, SourceCommandKind};
use fln_syntax::tree::Syntax;
use fln_vm::interpreter::{CancellationProbe, ExecutionUsage};
use fln_vm::macro_native::MacroLookup;

/// Explicit invocation state and ceilings for one source query. Reuse an
/// immutable registry or one of its scoped successors; no activation escapes
/// into another query.
pub struct SourceMacroInvocation<'a> {
    pub registry: &'a RegisteredMacros,
    pub context: &'a MacroContext,
    pub state: MacroState,
    /// Optional native read-only lookup override for this invocation. When it
    /// is absent, the Engine binds its own immutable environment, source module,
    /// and current namespace. An override is passed unchanged to every fallback,
    /// nested expansion and sibling and is never retained by the registry.
    pub lookup: Option<&'a dyn MacroLookup>,
    pub limits: MacroTreeLimits,
    pub cancellation: Option<&'a dyn CancellationProbe>,
}

#[derive(Debug)]
pub enum SourceMacroError {
    Binding(Box<MacroRegistrationError>),
    Execution(Box<MacroExecutionError>),
    Frontend(Box<EngineExecutionError>),
    Diagnostic {
        module: Name,
        declaration: Name,
        reference: Box<Syntax>,
        message: String,
    },
    AtomicExpansion {
        kind: Name,
    },
    TacticExpansion {
        kind: Name,
    },
    EvaluationRequired,
    DeclarationRequired,
}

impl std::fmt::Display for SourceMacroError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Binding(error) => write!(f, "source macro binding: {error}"),
            Self::Execution(error) => write!(f, "source macro execution: {error}"),
            Self::Frontend(error) => write!(f, "{error}"),
            Self::Diagnostic {
                module,
                declaration,
                message,
                ..
            } => write!(
                f,
                "macro {} from {}: {message}",
                declaration.to_display_string(),
                module.to_display_string()
            ),
            Self::AtomicExpansion { kind } => write!(
                f,
                "source macro adapter requires term elaborator dispatch for atomic kind {}",
                kind.to_display_string()
            ),
            Self::TacticExpansion { kind } => write!(
                f,
                "source macro adapter requires tactic evaluator dispatch for kind {}",
                kind.to_display_string()
            ),
            Self::EvaluationRequired => {
                write!(f, "source macro evaluation requires one ordinary #eval")
            }
            Self::DeclarationRequired => {
                write!(f, "source macro admission requires one named declaration")
            }
        }
    }
}

impl std::error::Error for SourceMacroError {}

/// A complete source check or a typed stop, together with the macro work that
/// actually ran. No successor environment is published. State is returned only
/// when both expansion and the ordinary source check completed successfully.
#[derive(Debug)]
pub struct SourceMacroCheck {
    pub outcome: Outcome<Result<SourceCheck, SourceMacroError>>,
    pub state: Option<MacroState>,
    pub attempts: Vec<MacroAttempt>,
    pub completed_vm_usage: ExecutionUsage,
}

/// Expanded source and the ordinary Engine execution, including its admission
/// observations, canonical FLBC and Golem's typed exit. As with ordinary #eval,
/// the generated unsafe declaration is quarantined: this is not a body-checked
/// proof or a safe logical declaration. The input Engine is
/// immutable; only this result retains the generated declaration's successor.
#[derive(Debug)]
pub struct SourceMacroEvaluationResult {
    pub parsed: ParsedSourceCommand,
    pub execution: DefinitionExecution,
}

/// Raw evaluation with an explicit imported macro table. A completed execution
/// may carry a non-returning VM exit; only a normal return publishes macro state.
#[derive(Debug)]
pub struct SourceMacroEvaluation {
    pub outcome: Outcome<Result<SourceMacroEvaluationResult, SourceMacroError>>,
    pub state: Option<MacroState>,
    pub attempts: Vec<MacroAttempt>,
    pub completed_vm_usage: ExecutionUsage,
}

/// Original source metadata and the ordinary declaration-admission receipts.
/// The successor includes attributes and separately checked local helpers, as
/// on `Engine::admit_source_declaration`. Inspect its actual checker ground:
/// safe definitions are body-checked, while unsafe declarations are quarantined.
#[derive(Debug)]
pub struct SourceMacroAdmissionResult {
    pub parsed: ParsedSourceCommand,
    pub admission: SourceDeclarationAdmission,
}

/// A named declaration produced by imported macros, or a typed stop. A failed
/// expansion/admission exposes neither an Engine successor nor macro state.
#[derive(Debug)]
pub struct SourceMacroAdmission {
    pub outcome: Outcome<Result<SourceMacroAdmissionResult, SourceMacroError>>,
    pub state: Option<MacroState>,
    pub attempts: Vec<MacroAttempt>,
    pub completed_vm_usage: ExecutionUsage,
}

struct Progress {
    state: Option<MacroState>,
    attempts: Vec<MacroAttempt>,
    usage: ExecutionUsage,
}

impl Engine {
    /// Expand an explicitly supplied imported node-macro table over one named
    /// declaration, then use the ordinary Engine's complete source-admission
    /// path. This publishes a usable immutable successor only after all
    /// declaration attributes and local helpers complete. No source text is
    /// rendered or reparsed, no parser descriptions are installed, and no VM
    /// evaluation of the admitted definition is requested.
    ///
    /// As on the query adapter, active atomic or tactic registrations that
    /// require elaborator dispatch remain explicit refusals. The entire
    /// declaration tree is visited, including its signature and body. Command
    /// wrapper changes into queries or scope commands are refused.
    pub fn admit_source_declaration_with_imported_macros(
        &self,
        source: &[u8],
        options: &KVMap,
        limits: EngineAdmissionLimits,
        invocation: SourceMacroInvocation<'_>,
    ) -> SourceMacroAdmission {
        let mut progress = Progress {
            state: None,
            attempts: Vec::new(),
            usage: ExecutionUsage {
                steps: 0,
                system_polls: 0,
                peak_stack_depth: 0,
            },
        };
        let outcome = match expand(
            self,
            source,
            SourceCommandKind::Definition,
            invocation,
            &mut progress,
        ) {
            Outcome::Complete(Ok((parsed, state))) => {
                match self.admit_source_syntax(source, parsed.syntax(), options, limits) {
                    Ok(Outcome::Complete(admission)) => {
                        progress.state = Some(state);
                        Outcome::Complete(Ok(SourceMacroAdmissionResult { parsed, admission }))
                    }
                    Ok(Outcome::Inconclusive(reason)) => Outcome::Inconclusive(reason),
                    Ok(Outcome::InternalFault(fault)) => Outcome::InternalFault(fault),
                    Err(error) => frontend(error),
                }
            }
            Outcome::Complete(Err(error)) => Outcome::Complete(Err(error)),
            Outcome::Inconclusive(reason) => Outcome::Inconclusive(reason),
            Outcome::InternalFault(fault) => Outcome::InternalFault(fault),
        };
        SourceMacroAdmission {
            outcome,
            state: progress.state,
            attempts: progress.attempts,
            completed_vm_usage: progress.usage,
        }
    }

    /// Parse one ordinary `#check`, execute an explicitly supplied checked
    /// imported node-macro table, and dual-check the expanded term.
    ///
    /// The source grammar is the same as `check_source_command`; this method
    /// does not enable additional parser registrations or compile source macros.
    /// It preserves source coordinates, pre-resolved identifiers and hygiene
    /// without printing and reparsing the expansion. Existing-global queries
    /// (`#check Nat`) retain the pin's signature shortcut and run no macro.
    ///
    /// Every registry owner, including inactive scoped entries, must still be
    /// the exact declaration of an admitted import in this engine. Additional
    /// source declarations do not invalidate that binding. Unless the caller
    /// supplies an explicit lookup override, native MacroM environment queries
    /// are answered from this Engine's immutable environment and base source
    /// scope for the duration of the call. Macro diagnostics, execution
    /// refusals, cancellation and resource stops never return a successful
    /// `SourceCheck` or a partially advanced macro state.
    pub fn check_source_command_with_imported_macros(
        &self,
        source: &[u8],
        options: &KVMap,
        admission: EngineAdmissionLimits,
        invocation: SourceMacroInvocation<'_>,
    ) -> SourceMacroCheck {
        let mut progress = Progress {
            state: None,
            attempts: Vec::new(),
            usage: ExecutionUsage {
                steps: 0,
                system_polls: 0,
                peak_stack_depth: 0,
            },
        };
        let outcome = match expand(
            self,
            source,
            SourceCommandKind::Check,
            invocation,
            &mut progress,
        ) {
            Outcome::Complete(Ok((parsed, state))) => {
                match self.check_parsed_source_command(parsed, options, admission, 0) {
                    Ok(Outcome::Complete(checked)) => {
                        progress.state = Some(state);
                        Outcome::Complete(Ok(checked))
                    }
                    Ok(Outcome::Inconclusive(reason)) => Outcome::Inconclusive(reason),
                    Ok(Outcome::InternalFault(fault)) => Outcome::InternalFault(fault),
                    Err(error) => frontend(error),
                }
            }
            Outcome::Complete(Err(error)) => Outcome::Complete(Err(error)),
            Outcome::Inconclusive(reason) => Outcome::Inconclusive(reason),
            Outcome::InternalFault(fault) => Outcome::InternalFault(fault),
        };
        SourceMacroCheck {
            outcome,
            state: progress.state,
            attempts: progress.attempts,
            completed_vm_usage: progress.usage,
        }
    }

    /// Expand an ordinary standalone `#eval` with the same checked imported
    /// table as the source-check door, then use the Engine's raw evaluation
    /// elaborator, dual-check admission, compiler, canonical codec and Golem.
    /// No printed expansion is reparsed. This is the raw embedding surface:
    /// it does not select a Repr printer or capture IO streams. Normal Engine
    /// execution limits apply to evaluation; the invocation's cancellation
    /// probe applies to expansion and is checked again before evaluation.
    /// Like the pin and the ordinary Engine evaluator, the generated definition
    /// is unsafe; its checker ground is `UnsafeQuarantine`, not body checking.
    pub fn evaluate_source_command_with_imported_macros(
        &self,
        source: &[u8],
        options: &KVMap,
        limits: EngineExecutionLimits,
        invocation: SourceMacroInvocation<'_>,
    ) -> SourceMacroEvaluation {
        let mut progress = Progress {
            state: None,
            attempts: Vec::new(),
            usage: ExecutionUsage {
                steps: 0,
                system_polls: 0,
                peak_stack_depth: 0,
            },
        };
        let outcome = match expand(
            self,
            source,
            SourceCommandKind::Evaluation,
            invocation,
            &mut progress,
        ) {
            Outcome::Complete(Ok((parsed, state))) => evaluate(self, parsed, options, limits)
                .map_complete(|result| {
                    if result.as_ref().is_ok_and(|result| {
                        matches!(
                            result.execution.exit,
                            fln_vm::interpreter::VmExit::Returned(_)
                        )
                    }) {
                        progress.state = Some(state);
                    }
                    result
                }),
            Outcome::Complete(Err(error)) => Outcome::Complete(Err(error)),
            Outcome::Inconclusive(reason) => Outcome::Inconclusive(reason),
            Outcome::InternalFault(fault) => Outcome::InternalFault(fault),
        };
        SourceMacroEvaluation {
            outcome,
            state: progress.state,
            attempts: progress.attempts,
            completed_vm_usage: progress.usage,
        }
    }
}

fn expand(
    engine: &Engine,
    source: &[u8],
    expected: SourceCommandKind,
    invocation: SourceMacroInvocation<'_>,
    progress: &mut Progress,
) -> Outcome<Result<(ParsedSourceCommand, MacroState), SourceMacroError>> {
    let SourceMacroInvocation {
        registry,
        context,
        state,
        lookup,
        limits,
        cancellation,
    } = invocation;
    if cancellation.is_some_and(CancellationProbe::is_cancelled) {
        return Outcome::Inconclusive(Inconclusive::cancelled("before imported source macros"));
    }
    if let Err(error) = registry.validate_source_engine(engine) {
        return Outcome::Complete(Err(SourceMacroError::Binding(Box::new(error))));
    }
    let allowed = limits.dispatch.execution.syntax.max_bytes;
    if source.len() > allowed {
        return Outcome::Inconclusive(
            Inconclusive::resource(ResourceUsage {
                reason: ResourceReason::Memory {
                    limit_bytes: allowed as u64,
                },
                allowed: allowed as u64,
                observed: source.len() as u64,
            })
            .with_progress("imported source macro bytes"),
        );
    }
    let parsed = match fln_parse::parse_source_command(source) {
        Ok(parsed) => parsed,
        Err(error) => {
            return frontend(EngineExecutionError::Frontend(
                crate::DefinitionFrontendError::Parse(error),
            ));
        }
    };
    let command = match expected {
        SourceCommandKind::Check => "check",
        SourceCommandKind::Definition => "declaration",
        _ => "eval",
    };
    let Syntax::Node { kind, args, .. } = parsed.syntax() else {
        return wrong_command(expected);
    };
    if *kind != Name::from_components(["Lean", "Parser", "Command", command])
        || args.len() != 2
        || parsed.kind() != expected
    {
        return wrong_command(expected);
    }
    let input = if expected == SourceCommandKind::Definition {
        parsed.syntax()
    } else {
        &args[1]
    };
    let scope = engine.base_source_scope();
    // Production source checks should not require the embedding caller to
    // reconstruct the Macro.Methods environment capability that the Engine
    // already owns. Bind a fresh borrowed provider to this immutable snapshot.
    // Standalone source has no module identity; the anonymous module cannot
    // accidentally select a foreign private declaration.
    let anonymous_module = Name::anonymous();
    let main_module = scope
        .source_module
        .as_ref()
        .or(scope.private_module.as_ref())
        .unwrap_or(&anonymous_module);
    let engine_lookup =
        EnvironmentMacroLookup::new(engine.environment(), main_module, &scope.namespace);
    let lookup = lookup.or(Some(&engine_lookup as &dyn MacroLookup));
    let resolve = crate::source_check::grammar::resolver(engine.environment(), &scope);
    let existing_global = expected == SourceCommandKind::Check
        && parsed.query_is_identifier()
        && matches!(input, Syntax::Ident { val, .. }
            if matches!(resolve(val),
                crate::source_check::grammar::Resolution::Global(_)
                | crate::source_check::grammar::Resolution::Constructor(_)));
    let (parsed, state) = if existing_global {
        (parsed, state)
    } else {
        // Parse once, then expand the term before any parser template could
        // erase the node the imported table is meant to see.
        let expanded = registry.expand_tree_with_context(
            input,
            MacroDispatchInvocation {
                source: parsed.source_view().normalized(),
                context,
                state,
                lookup,
            },
            limits,
            cancellation,
        );
        progress.attempts = expanded.attempts;
        progress.usage = expanded.completed_vm_usage;
        let (syntax, state) = match expanded.outcome {
            Outcome::Complete(Ok(MacroTreeResult::Expanded { syntax, state })) => (syntax, state),
            Outcome::Complete(Ok(MacroTreeResult::Error {
                module,
                declaration,
                reference,
                message,
                ..
            })) => {
                return Outcome::Complete(Err(SourceMacroError::Diagnostic {
                    module,
                    declaration,
                    reference: Box::new(reference),
                    message,
                }));
            }
            Outcome::Complete(Err(error)) => {
                return Outcome::Complete(Err(SourceMacroError::Execution(Box::new(error))));
            }
            Outcome::Inconclusive(reason) => return Outcome::Inconclusive(reason),
            Outcome::InternalFault(fault) => return Outcome::InternalFault(fault),
        };
        // expandMacros deliberately leaves atomic syntax alone. Silently
        // ignoring an active atomic registration would claim a different
        // source meaning, so retain an explicit boundary until term elaboration
        // itself can invoke the imported table.
        match deferred_candidate(registry, &syntax) {
            Ok(Some(error)) => return Outcome::Complete(Err(error)),
            Ok(None) => {}
            Err(reason) => return Outcome::Inconclusive(reason),
        }
        let rewritten = if expected == SourceCommandKind::Definition {
            parsed.with_expanded_declaration(syntax)
        } else {
            parsed.with_expanded_query_term(syntax)
        };
        let Some(parsed) = rewritten else {
            return wrong_command(expected);
        };
        (parsed, state)
    };
    if cancellation.is_some_and(CancellationProbe::is_cancelled) {
        return Outcome::Inconclusive(Inconclusive::cancelled(
            "after imported source macros, before source elaboration",
        ));
    }
    Outcome::Complete(Ok((parsed, state)))
}

fn evaluate(
    engine: &Engine,
    parsed: ParsedSourceCommand,
    options: &KVMap,
    limits: EngineExecutionLimits,
) -> Outcome<Result<SourceMacroEvaluationResult, SourceMacroError>> {
    let run = || -> Result<Outcome<DefinitionExecution>, EngineExecutionError> {
        let mut scope = engine.base_source_scope();
        scope.source_site = Some(crate::source_check::source_site(
            &parsed.reconstruct_original(),
        )?);
        let name = crate::fresh_generated_command_name(engine.environment(), 0)?;
        let (declaration, _) = match crate::source_evaluation::elaborate(
            engine,
            parsed.syntax(),
            name,
            &scope,
            options,
            limits,
            crate::EvaluationPresentation::Raw,
        )? {
            Outcome::Complete(result) => result,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        if crate::source_execution::evaluation_depends_on_sorry(
            engine,
            std::iter::once(&declaration),
        )? {
            return Err(EngineExecutionError::EvaluationDependsOnSorry);
        }
        engine.execute_definition_entry(
            declaration,
            options,
            limits,
            crate::source_evaluation::Entry::Evaluation,
        )
    };
    match run() {
        Ok(outcome) => {
            outcome.map_complete(|execution| Ok(SourceMacroEvaluationResult { parsed, execution }))
        }
        Err(error) => frontend(error),
    }
}

fn wrong_command<T>(expected: SourceCommandKind) -> Outcome<Result<T, SourceMacroError>> {
    if expected == SourceCommandKind::Check {
        frontend(EngineExecutionError::StandaloneCheckRequired)
    } else if expected == SourceCommandKind::Definition {
        Outcome::Complete(Err(SourceMacroError::DeclarationRequired))
    } else {
        Outcome::Complete(Err(SourceMacroError::EvaluationRequired))
    }
}

fn frontend<T>(error: EngineExecutionError) -> Outcome<Result<T, SourceMacroError>> {
    Outcome::Complete(Err(SourceMacroError::Frontend(Box::new(error))))
}

/// The complete result was already checked against the Syntax conversion
/// ceilings. This additional walk detects registrations that still require
/// term or tactic elaborator dispatch; it does not expand again.
fn deferred_candidate(
    registry: &RegisteredMacros,
    syntax: &Syntax,
) -> Result<Option<SourceMacroError>, Inconclusive> {
    let tactic = Name::from_components(["Lean", "Parser", "Term", "byTactic"]);
    let mut pending = vec![(syntax, false)];
    while let Some((syntax, in_tactic)) = pending.pop() {
        let kind = match syntax {
            Syntax::Node { kind, args, .. } => {
                let in_tactic = in_tactic || *kind == tactic;
                if in_tactic && registry.declarations(kind).next().is_some() {
                    return Ok(Some(SourceMacroError::TacticExpansion {
                        kind: kind.clone(),
                    }));
                }
                pending.try_reserve(args.len()).map_err(|_| {
                    Inconclusive::dependency_unavailable(
                        "source macro deferred boundary allocation",
                    )
                })?;
                pending.extend(args.iter().map(|argument| (argument, in_tactic)));
                continue;
            }
            Syntax::Ident { .. } => Name::from_components(["ident"]),
            Syntax::Missing => Name::from_components(["missing"]),
            Syntax::Atom { val, .. } => Name::str(Name::anonymous(), val),
        };
        if registry.declarations(&kind).next().is_some() {
            return Ok(Some(SourceMacroError::AtomicExpansion { kind }));
        }
    }
    Ok(None)
}
