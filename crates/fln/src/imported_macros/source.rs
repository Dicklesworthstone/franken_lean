//! Imported node macros on source declarations, anonymous examples, `#check` and raw `#eval`.
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
    MacroTreeResult, MacroTreeUsage, RegisteredMacros,
};
use super::{MacroContext, MacroExecutionError, MacroState};
use crate::source_check::{SourceCheckError, SourceCheckLimits, SourceFileCheck};
use crate::{
    DefinitionExecution, Engine, EngineAdmissionLimits, EngineExecutionError,
    EngineExecutionLimits, SourceCheck, SourceDeclarationAdmission,
};
use fln_core::diag::ResourceReason;
use fln_core::name::Name;
use fln_core::options::KVMap;
use fln_core::outcome::{Inconclusive, Outcome, ResourceUsage};
use fln_parse::{ParsedSourceCommand, SourceCommandKind};
use fln_syntax::source::SourceText;
use fln_syntax::tree::Syntax;
use fln_syntax::view::SourceView;
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
    ExampleRequired,
    TemplateGrammar,
    ScopeControl {
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
            Self::EvaluationRequired => {
                write!(f, "source macro evaluation requires one ordinary #eval")
            }
            Self::DeclarationRequired => {
                write!(f, "source macro admission requires one named declaration")
            }
            Self::ExampleRequired => {
                write!(f, "source macro checking requires an anonymous example")
            }
            Self::TemplateGrammar => write!(
                f,
                "imported macro file checking requires a grammar without source-declared templates"
            ),
            Self::ScopeControl { kind } => write!(
                f,
                "source macro adapter cannot apply an expanded scope control of kind {}",
                kind.to_display_string()
            ),
        }
    }
}

impl std::error::Error for SourceMacroError {}

impl SourceMacroError {
    pub(crate) fn disposition(&self) -> (&'static str, bool, u8) {
        match self {
            Self::Frontend(error) => crate::source_check::classify(error),
            Self::Binding(error) if error.is_resource() => ("resource", false, 3),
            Self::Execution(error)
                if matches!(error.as_ref(),
                MacroExecutionError::Compile(error) if error.is_resource()) =>
            {
                ("resource", false, 3)
            }
            Self::Diagnostic { .. } => ("macro", false, 1),
            _ => ("capability", false, 5),
        }
    }
}

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

/// An admission-only file batch and its actual macro work. A failed command
/// exposes neither the successful prefix's Engine nor a successor MacroState.
#[derive(Debug)]
pub struct SourceMacroFileCheck {
    pub outcome: Outcome<Result<SourceFileCheck, SourceCheckError>>,
    pub state: Option<MacroState>,
    pub attempts: Vec<MacroAttempt>,
    pub completed_vm_usage: ExecutionUsage,
    pub tree_usage: MacroTreeUsage,
}

struct Progress {
    state: Option<MacroState>,
    attempts: Vec<MacroAttempt>,
    usage: ExecutionUsage,
    tree_usage: MacroTreeUsage,
}

/// One private transaction across all files. Lexical registry activation lives
/// in the ordinary scope stack; state and work allowances survive scope exits
/// and file boundaries and are returned only with a complete checked batch.
pub(crate) struct FileSession<'a> {
    registry: &'a RegisteredMacros,
    context: &'a MacroContext,
    state: MacroState,
    lookup: Option<&'a dyn MacroLookup>,
    limits: MacroTreeLimits,
    cancellation: Option<&'a dyn CancellationProbe>,
    progress: Progress,
}

impl<'a> FileSession<'a> {
    fn new(invocation: SourceMacroInvocation<'a>) -> Self {
        Self {
            registry: invocation.registry,
            context: invocation.context,
            state: invocation.state,
            lookup: invocation.lookup,
            limits: invocation.limits,
            cancellation: invocation.cancellation,
            progress: Progress {
                state: None,
                attempts: Vec::new(),
                usage: ExecutionUsage {
                    steps: 0,
                    system_polls: 0,
                    peak_stack_depth: 0,
                },
                tree_usage: MacroTreeUsage::default(),
            },
        }
    }

    pub(crate) fn registry(&self) -> RegisteredMacros {
        self.registry.clone()
    }

    pub(crate) fn cancelled(&self) -> Option<Inconclusive> {
        self.cancellation
            .is_some_and(CancellationProbe::is_cancelled)
            .then(|| Inconclusive::cancelled("imported macro source batch"))
    }

    /// Native scope transitions do not interpret arbitrary expanded command
    /// trees. Refuse an active registration instead of silently bypassing it,
    /// including transitions introduced by an `in` wrapper.
    pub(crate) fn check_native_control(
        &self,
        registry: &RegisteredMacros,
        control: &fln_parse::command_scope::ScopeCommand,
    ) -> Result<(), SourceMacroError> {
        use fln_parse::command_scope::ScopeCommand;
        let command = match control {
            ScopeCommand::Variable(_) | ScopeCommand::Executable(_) | ScopeCommand::Trivia => {
                return Ok(());
            }
            ScopeCommand::Namespace(_) => "namespace",
            ScopeCommand::Section(_) | ScopeCommand::SectionWithModifiers { .. } => "section",
            ScopeCommand::End(_) => "end",
            ScopeCommand::Open(_)
            | ScopeCommand::OpenScoped(_)
            | ScopeCommand::OpenExplicit { .. } => "open",
            ScopeCommand::Universe(_) => "universe",
            ScopeCommand::Include(_) => "include",
            ScopeCommand::Omit(_) => "omit",
            ScopeCommand::Simp(_) | ScopeCommand::Instance(_) | ScopeCommand::Reducibility(_) => {
                "attribute"
            }
            ScopeCommand::OpenIn { .. }
            | ScopeCommand::SetOptionIn { .. }
            | ScopeCommand::In { .. } => "in",
            ScopeCommand::SetOption { .. } => "set_option",
            ScopeCommand::Export { .. } => "export",
            ScopeCommand::Exit => "exit",
            ScopeCommand::GuardMsgs { .. } => return Ok(()), // Already refused by this front door.
        };
        let kind = Name::from_components(["Lean", "Parser", "Command", command]);
        if registry.declarations(&kind).next().is_some() {
            return Err(SourceMacroError::ScopeControl { kind });
        }
        // `open` is a wrapper around its actual open declaration. Native
        // lowering must not silently discard a macro on that child either.
        // Inspect only the head of an `in` wrapper, never its pending body.
        let nested: &[&str] = match control {
            ScopeCommand::Open(_) => &["openSimple"],
            ScopeCommand::OpenScoped(_) => &["openScoped"],
            ScopeCommand::OpenExplicit { .. } => &["openOnly"],
            ScopeCommand::OpenIn { scoped: true, .. } => &["open", "openScoped"],
            ScopeCommand::OpenIn { scoped: false, .. } => &["open", "openSimple"],
            ScopeCommand::SetOptionIn { .. } => &["set_option"],
            _ => &[],
        };
        for command in nested {
            let kind = Name::from_components(["Lean", "Parser", "Command", command]);
            if registry.declarations(&kind).next().is_some() {
                return Err(SourceMacroError::ScopeControl { kind });
            }
        }
        // The parser's optionValue alternative emits a bare literal node or
        // boolean atom, without an optionValue wrapper.
        let value_kind = match control {
            ScopeCommand::SetOption { value, .. } | ScopeCommand::SetOptionIn { value, .. } => {
                match value {
                    fln_core::options::DataValue::OfNat(_) => Some("num"),
                    fln_core::options::DataValue::OfString(_) => Some("str"),
                    fln_core::options::DataValue::OfBool(true) => Some("true"),
                    fln_core::options::DataValue::OfBool(false) => Some("false"),
                    _ => None,
                }
            }
            _ => None,
        };
        if let Some(value_kind) = value_kind {
            let kind = Name::from_components([value_kind]);
            if registry.declarations(&kind).next().is_some() {
                return Err(SourceMacroError::ScopeControl { kind });
            }
        }
        Ok(())
    }

    pub(crate) fn expand_command(
        &mut self,
        engine: &Engine,
        registry: &RegisteredMacros,
        source: &[u8],
        scope: &fln_elab::source::scope::SourceScope,
    ) -> Outcome<Result<crate::source_records::ScopedCommandSyntax, SourceMacroError>> {
        use crate::source_records::ScopedCommandSyntax;
        match source_preflight(engine, registry, source, self.limits, self.cancellation) {
            Outcome::Complete(Ok(())) => {}
            Outcome::Complete(Err(error)) => return Outcome::Complete(Err(error)),
            Outcome::Inconclusive(reason) => return Outcome::Inconclusive(reason),
            Outcome::InternalFault(fault) => return Outcome::InternalFault(fault),
        }
        let parsed = match crate::source_records::parse_scoped_command_without_expansion(source) {
            Ok(parsed) => parsed,
            Err(error) => return frontend(error),
        };
        match parsed {
            ScopedCommandSyntax::Mutual(mut members) => {
                let view = match source_view(source) {
                    Ok(view) => view,
                    Err(error) => return Outcome::Complete(Err(error)),
                };
                // Mutual members see the group's original predecessor, while
                // macro state and budgets advance in their source order. The
                // whole group is admitted only after all expansions succeed.
                for member in &mut members {
                    match self.expand_syntax(engine, registry, view.normalized(), member, scope) {
                        Outcome::Complete(Ok(syntax)) => {
                            if !matches!(&syntax, Syntax::Node { kind, args, .. }
                                if *kind == Name::from_components(["Lean", "Parser", "Command", "declaration"])
                                    && args.len() == 2)
                                || fln_elab::source::scope::is_example(&syntax)
                            {
                                return wrong_command(SourceCommandKind::Definition);
                            }
                            *member = syntax;
                        }
                        Outcome::Complete(Err(error)) => return Outcome::Complete(Err(error)),
                        Outcome::Inconclusive(reason) => return Outcome::Inconclusive(reason),
                        Outcome::InternalFault(fault) => return Outcome::InternalFault(fault),
                    }
                }
                Outcome::Complete(Ok(ScopedCommandSyntax::Mutual(members)))
            }
            ScopedCommandSyntax::Example(parsed) => self
                .expand_syntax(
                    engine,
                    registry,
                    parsed.source_view().normalized(),
                    parsed.syntax(),
                    scope,
                )
                .map_complete(|result| {
                    result.and_then(|syntax| {
                        parsed
                            .with_expanded_example(syntax)
                            .map(ScopedCommandSyntax::Example)
                            .ok_or(SourceMacroError::ExampleRequired)
                    })
                }),
            ScopedCommandSyntax::Definition(parsed) => self
                .expand_syntax(
                    engine,
                    registry,
                    parsed.source_view().normalized(),
                    parsed.syntax(),
                    scope,
                )
                .map_complete(|result| {
                    result.and_then(|syntax| {
                        parsed
                            .with_expanded_syntax(syntax)
                            .map(ScopedCommandSyntax::Definition)
                            .ok_or(SourceMacroError::DeclarationRequired)
                    })
                }),
        }
    }

    /// Expand the parser's existing binder/attribute tree, using its original
    /// normalized backing source. Native namespace and option controls retain
    /// their ordinary scope semantics; they do not enter command-macro dispatch.
    pub(crate) fn expand_control(
        &mut self,
        engine: &Engine,
        registry: &RegisteredMacros,
        source: &[u8],
        control: fln_parse::command_scope::ScopeCommand,
        scope: &fln_elab::source::scope::SourceScope,
    ) -> Outcome<Result<fln_parse::command_scope::ScopeCommand, SourceMacroError>> {
        use fln_parse::command_scope::ScopeCommand;
        let (syntax, variable) = match control {
            ScopeCommand::Variable(syntax) => (syntax, true),
            ScopeCommand::Executable(syntax) => (syntax, false),
            other => return Outcome::Complete(Ok(other)),
        };
        match source_preflight(engine, registry, source, self.limits, self.cancellation) {
            Outcome::Complete(Ok(())) => {}
            Outcome::Complete(Err(error)) => return Outcome::Complete(Err(error)),
            Outcome::Inconclusive(reason) => return Outcome::Inconclusive(reason),
            Outcome::InternalFault(fault) => return Outcome::InternalFault(fault),
        }
        let view = match source_view(source) {
            Ok(view) => view,
            Err(error) => return Outcome::Complete(Err(error)),
        };
        // Variables were parsed into a binder-only control payload. Recover
        // the original canonical command tree before expansion so a registered
        // Command.variable macro participates, just as an attribute root does.
        let variable_kind = Name::from_components(["Lean", "Parser", "Command", "variable"]);
        let syntax = if variable {
            match fln_parse::command_scope::trees::tree(source) {
                Ok(Some(syntax)) => syntax,
                Ok(None) => {
                    return Outcome::Complete(Err(SourceMacroError::ScopeControl {
                        kind: variable_kind,
                    }));
                }
                Err(error) => {
                    return frontend(EngineExecutionError::Frontend(
                        crate::DefinitionFrontendError::Parse(error),
                    ));
                }
            }
        } else {
            syntax
        };
        self.expand_syntax(engine, registry, view.normalized(), &syntax, scope)
            .map_complete(|result| {
                result.and_then(|mut syntax| {
                    if variable {
                        if let Syntax::Node { kind, args, .. } = &mut syntax
                            && *kind == variable_kind
                            && args.len() == 2
                            && let Some(binders) = args.pop()
                        {
                            return Ok(ScopeCommand::Variable(binders));
                        }
                        Err(SourceMacroError::ScopeControl {
                            kind: variable_kind,
                        })
                    } else {
                        Ok(ScopeCommand::Executable(syntax))
                    }
                })
            })
    }

    fn expand_syntax(
        &mut self,
        engine: &Engine,
        registry: &RegisteredMacros,
        source: &SourceText,
        syntax: &Syntax,
        scope: &fln_elab::source::scope::SourceScope,
    ) -> Outcome<Result<Syntax, SourceMacroError>> {
        let mut remaining = self.limits;
        remaining.dispatch.max_attempts = remaining
            .dispatch
            .max_attempts
            .saturating_sub(self.progress.attempts.len() as u64);
        remaining.dispatch.execution.vm.max_steps = remaining
            .dispatch
            .execution
            .vm
            .max_steps
            .saturating_sub(self.progress.usage.steps);
        remaining.max_visits = remaining
            .max_visits
            .saturating_sub(self.progress.tree_usage.visits);
        remaining.generation.max_nodes = remaining
            .generation
            .max_nodes
            .saturating_sub(self.progress.tree_usage.generated_nodes);
        remaining.generation.max_bytes = remaining
            .generation
            .max_bytes
            .saturating_sub(self.progress.tree_usage.generated_bytes);
        let mut progress = Progress {
            state: None,
            attempts: Vec::new(),
            usage: ExecutionUsage {
                steps: 0,
                system_polls: 0,
                peak_stack_depth: 0,
            },
            tree_usage: MacroTreeUsage::default(),
        };
        let expanded = expand_syntax_in_scope(
            engine,
            source,
            syntax,
            scope,
            SourceMacroInvocation {
                registry,
                context: self.context,
                state: std::mem::take(&mut self.state),
                lookup: self.lookup,
                limits: remaining,
                cancellation: self.cancellation,
            },
            &mut progress,
        );
        if let Err(reason) = self.record(progress) {
            return Outcome::Inconclusive(reason);
        }
        expanded.map_complete(|result| {
            result.map(|(syntax, state)| {
                self.state = state;
                syntax
            })
        })
    }

    fn record(&mut self, mut progress: Progress) -> Result<(), Inconclusive> {
        let overflow =
            || Inconclusive::dependency_unavailable("imported macro batch usage overflow");
        self.progress.usage.steps = self
            .progress
            .usage
            .steps
            .checked_add(progress.usage.steps)
            .ok_or_else(overflow)?;
        self.progress.usage.system_polls = self
            .progress
            .usage
            .system_polls
            .checked_add(progress.usage.system_polls)
            .ok_or_else(overflow)?;
        self.progress.usage.peak_stack_depth = self
            .progress
            .usage
            .peak_stack_depth
            .max(progress.usage.peak_stack_depth);
        self.progress.tree_usage.visits = self
            .progress
            .tree_usage
            .visits
            .checked_add(progress.tree_usage.visits)
            .ok_or_else(overflow)?;
        self.progress.tree_usage.generated_nodes = self
            .progress
            .tree_usage
            .generated_nodes
            .checked_add(progress.tree_usage.generated_nodes)
            .ok_or_else(overflow)?;
        self.progress.tree_usage.generated_bytes = self
            .progress
            .tree_usage
            .generated_bytes
            .checked_add(progress.tree_usage.generated_bytes)
            .ok_or_else(overflow)?;
        self.progress
            .attempts
            .try_reserve(progress.attempts.len())
            .map_err(|_| {
                Inconclusive::dependency_unavailable("imported macro batch attempt allocation")
            })?;
        self.progress.attempts.append(&mut progress.attempts);
        Ok(())
    }
}

impl Engine {
    /// Check declaration files with an explicitly prepared imported-macro
    /// registry. The ordinary file driver owns namespaces, sections, opens,
    /// attributes, declaration admission and anonymous-example checking.
    /// Scoped registrations follow those exact lexical lifetimes; later macros
    /// observe earlier admitted declarations through the native lookup provider.
    ///
    /// Attempts, VM steps, syntax visits and generated syntax share one budget
    /// across the complete batch. Each file restores the initial registry's
    /// activation, while MacroState continues in command order. No failed prefix
    /// is published. Variable binders, executable attributes and mutual members
    /// use the same expansion pass. Native scope controls retain their ordinary
    /// semantics without command-root macro dispatch. Source-declared templates,
    /// artifact parser installation and module-system visibility remain separate
    /// capabilities.
    pub fn check_source_files_with_imported_macros(
        &self,
        sources: &[&[u8]],
        options: &KVMap,
        limits: SourceCheckLimits,
        invocation: SourceMacroInvocation<'_>,
    ) -> SourceMacroFileCheck {
        let mut session = FileSession::new(invocation);
        let outcome = if let Err(error) = session.registry.validate_source_engine(self) {
            Outcome::Complete(Err(SourceCheckError::ImportedMacro {
                file: 0,
                command: 0,
                offset: 0,
                error: Box::new(SourceMacroError::Binding(Box::new(error))),
            }))
        } else {
            match self.check_source_files_recording(
                sources,
                options,
                limits,
                None,
                None,
                None,
                None,
                None,
                Some(&mut session),
            ) {
                Ok(outcome) => outcome.map_complete(Ok),
                Err(error) => Outcome::Complete(Err(error)),
            }
        };
        let state = matches!(&outcome, Outcome::Complete(Ok(_))).then_some(session.state);
        SourceMacroFileCheck {
            outcome,
            state,
            attempts: session.progress.attempts,
            completed_vm_usage: session.progress.usage,
            tree_usage: session.progress.tree_usage,
        }
    }

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
            tree_usage: MacroTreeUsage::default(),
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

    /// Parse one ordinary `#check` or anonymous `example`, execute an explicitly
    /// supplied checked imported node-macro table, and dual-check the expansion.
    /// Examples expand their binders, signature and body, then discard the
    /// scratch checker successor just as ordinary source examples do.
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
            tree_usage: MacroTreeUsage::default(),
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
            tree_usage: MacroTreeUsage::default(),
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
    expand_in_scope(
        engine,
        source,
        Some(expected),
        &engine.base_source_scope(),
        invocation,
        progress,
    )
}

fn expand_in_scope(
    engine: &Engine,
    source: &[u8],
    expected: Option<SourceCommandKind>,
    scope: &fln_elab::source::scope::SourceScope,
    invocation: SourceMacroInvocation<'_>,
    progress: &mut Progress,
) -> Outcome<Result<(ParsedSourceCommand, MacroState), SourceMacroError>> {
    match source_preflight(
        engine,
        invocation.registry,
        source,
        invocation.limits,
        invocation.cancellation,
    ) {
        Outcome::Complete(Ok(())) => {}
        Outcome::Complete(Err(error)) => return Outcome::Complete(Err(error)),
        Outcome::Inconclusive(reason) => return Outcome::Inconclusive(reason),
        Outcome::InternalFault(fault) => return Outcome::InternalFault(fault),
    }
    let parsed = match fln_parse::parse_source_command(source) {
        Ok(parsed) => parsed,
        Err(error) => {
            return frontend(EngineExecutionError::Frontend(
                crate::DefinitionFrontendError::Parse(error),
            ));
        }
    };
    let expected = match expected {
        Some(SourceCommandKind::Check) if parsed.kind() == SourceCommandKind::Example => {
            SourceCommandKind::Example
        }
        Some(expected) => expected,
        None if matches!(
            parsed.kind(),
            SourceCommandKind::Definition | SourceCommandKind::Example
        ) =>
        {
            parsed.kind()
        }
        None => return wrong_command(SourceCommandKind::Definition),
    };
    let declaration = matches!(
        expected,
        SourceCommandKind::Definition | SourceCommandKind::Example
    );
    let command = match expected {
        SourceCommandKind::Check => "check",
        SourceCommandKind::Definition | SourceCommandKind::Example => "declaration",
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
    let input = if declaration {
        parsed.syntax()
    } else {
        &args[1]
    };
    let resolve = crate::source_check::grammar::resolver(engine.environment(), scope);
    let existing_global = expected == SourceCommandKind::Check
        && parsed.query_is_identifier()
        && matches!(input, Syntax::Ident { val, .. }
            if matches!(resolve(val),
                crate::source_check::grammar::Resolution::Global(_)
                | crate::source_check::grammar::Resolution::Constructor(_)));
    let (parsed, state) = if existing_global {
        if invocation
            .cancellation
            .is_some_and(CancellationProbe::is_cancelled)
        {
            return Outcome::Inconclusive(Inconclusive::cancelled(
                "after imported source macros, before source elaboration",
            ));
        }
        (parsed, invocation.state)
    } else {
        // Parse once, then expand the term before any parser template could
        // erase the node the imported table is meant to see.
        let expanded = expand_syntax_in_scope(
            engine,
            parsed.source_view().normalized(),
            input,
            scope,
            invocation,
            progress,
        );
        let (syntax, state) = match expanded {
            Outcome::Complete(Ok(result)) => result,
            Outcome::Complete(Err(error)) => return Outcome::Complete(Err(error)),
            Outcome::Inconclusive(reason) => return Outcome::Inconclusive(reason),
            Outcome::InternalFault(fault) => return Outcome::InternalFault(fault),
        };
        let rewritten = match expected {
            SourceCommandKind::Definition => parsed.with_expanded_declaration(syntax),
            SourceCommandKind::Example => parsed.with_expanded_example(syntax),
            _ => parsed.with_expanded_query_term(syntax),
        };
        let Some(parsed) = rewritten else {
            return wrong_command(expected);
        };
        (parsed, state)
    };
    Outcome::Complete(Ok((parsed, state)))
}

fn source_view(source: &[u8]) -> Result<SourceView, SourceMacroError> {
    SourceText::from_utf8(source)
        .map(|text| SourceView::of(&text))
        .map_err(|error| {
            SourceMacroError::Frontend(Box::new(EngineExecutionError::Frontend(
                crate::DefinitionFrontendError::Parse(fln_parse::DefinitionParseError::Source(
                    error,
                )),
            )))
        })
}

fn source_preflight(
    engine: &Engine,
    registry: &RegisteredMacros,
    source: &[u8],
    limits: MacroTreeLimits,
    cancellation: Option<&dyn CancellationProbe>,
) -> Outcome<Result<(), SourceMacroError>> {
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
    Outcome::Complete(Ok(()))
}

/// The one executable expansion pass for queries, declarations, mutual members
/// and syntax-bearing controls. The caller has validated the source binding and
/// byte ceiling before parsing; this pass neither prints nor reparses Syntax.
fn expand_syntax_in_scope(
    engine: &Engine,
    source: &SourceText,
    input: &Syntax,
    scope: &fln_elab::source::scope::SourceScope,
    invocation: SourceMacroInvocation<'_>,
    progress: &mut Progress,
) -> Outcome<Result<(Syntax, MacroState), SourceMacroError>> {
    let SourceMacroInvocation {
        registry,
        context,
        state,
        lookup,
        limits,
        cancellation,
    } = invocation;
    // Bind native Macro.Methods to this exact immutable predecessor and scope.
    // An anonymous module cannot select a foreign private declaration.
    let anonymous_module = Name::anonymous();
    let main_module = scope
        .source_module
        .as_ref()
        .or(scope.private_module.as_ref())
        .unwrap_or(&anonymous_module);
    let engine_lookup = EnvironmentMacroLookup::new(
        engine.environment(),
        main_module,
        &scope.namespace,
        &scope.opened,
        &scope.explicit_opens,
    );
    let lookup = lookup.or(Some(&engine_lookup as &dyn MacroLookup));
    let expanded = registry.expand_tree_with_context(
        input,
        MacroDispatchInvocation {
            source,
            context,
            state,
            lookup,
        },
        limits,
        cancellation,
    );
    progress.attempts = expanded.attempts;
    progress.usage = expanded.completed_vm_usage;
    progress.tree_usage = expanded.usage;
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
    // Atomic and tactic dispatch belongs to their elaborators. Do not silently
    // ignore a registration that this recursive expansion pass leaves behind.
    match deferred_candidate(registry, &syntax) {
        Ok(Some(error)) => return Outcome::Complete(Err(error)),
        Ok(None) => {}
        Err(reason) => return Outcome::Inconclusive(reason),
    }
    if cancellation.is_some_and(CancellationProbe::is_cancelled) {
        return Outcome::Inconclusive(Inconclusive::cancelled(
            "after imported source macros, before source elaboration",
        ));
    }
    Outcome::Complete(Ok((syntax, state)))
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
    } else if expected == SourceCommandKind::Example {
        Outcome::Complete(Err(SourceMacroError::ExampleRequired))
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
