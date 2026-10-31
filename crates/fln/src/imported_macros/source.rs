//! Checked imported node macros on the standalone source `#check` path.
//!
//! This is an explicit embedding door for syntax the current parser already
//! understands. It installs no artifact parser descriptions. The prepared
//! registry owns the expansion pass: no template expansion runs before it or
//! replays its results. The resulting native Syntax enters the same elaborator
//! and dual-check admission as `Engine::check_source_command`.
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
use crate::{Engine, EngineAdmissionLimits, EngineExecutionError, SourceCheck};
use fln_core::diag::ResourceReason;
use fln_core::name::Name;
use fln_core::options::KVMap;
use fln_core::outcome::{Inconclusive, Outcome, ResourceUsage};
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
        reference: Syntax,
        message: String,
    },
    AtomicExpansion {
        kind: Name,
    },
    TacticExpansion {
        kind: Name,
    },
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

struct Progress {
    state: Option<MacroState>,
    attempts: Vec<MacroAttempt>,
    usage: ExecutionUsage,
}

impl Engine {
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
        let outcome = check(self, source, options, admission, invocation, &mut progress);
        SourceMacroCheck {
            outcome,
            state: progress.state,
            attempts: progress.attempts,
            completed_vm_usage: progress.usage,
        }
    }
}

fn check(
    engine: &Engine,
    source: &[u8],
    options: &KVMap,
    admission: EngineAdmissionLimits,
    invocation: SourceMacroInvocation<'_>,
    progress: &mut Progress,
) -> Outcome<Result<SourceCheck, SourceMacroError>> {
    let SourceMacroInvocation {
        registry,
        context,
        state,
        lookup,
        limits,
        cancellation,
    } = invocation;
    if cancellation.is_some_and(CancellationProbe::is_cancelled) {
        return Outcome::Inconclusive(Inconclusive::cancelled(
            "before imported source macro check",
        ));
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
    let Syntax::Node { kind, args, .. } = parsed.syntax() else {
        return frontend(EngineExecutionError::StandaloneCheckRequired);
    };
    if *kind != Name::from_components(["Lean", "Parser", "Command", "check"])
        || args.len() != 2
        || parsed.kind() != fln_parse::SourceCommandKind::Check
    {
        return frontend(EngineExecutionError::StandaloneCheckRequired);
    }
    let input = &args[1];
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
    let existing_global = parsed.query_is_identifier()
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
                    reference,
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
        let Some(parsed) = parsed.with_expanded_check_term(syntax) else {
            return frontend(EngineExecutionError::StandaloneCheckRequired);
        };
        (parsed, state)
    };
    if cancellation.is_some_and(CancellationProbe::is_cancelled) {
        return Outcome::Inconclusive(Inconclusive::cancelled(
            "after imported source macros, before source checking",
        ));
    }
    match engine.check_parsed_source_command(parsed, options, admission, 0) {
        Ok(Outcome::Complete(checked)) => {
            progress.state = Some(state);
            Outcome::Complete(Ok(checked))
        }
        Ok(Outcome::Inconclusive(reason)) => Outcome::Inconclusive(reason),
        Ok(Outcome::InternalFault(fault)) => Outcome::InternalFault(fault),
        Err(error) => frontend(error),
    }
}

fn frontend(error: EngineExecutionError) -> Outcome<Result<SourceCheck, SourceMacroError>> {
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
