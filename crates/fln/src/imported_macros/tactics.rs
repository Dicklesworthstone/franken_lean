//! Owned bridge from source scope to the checked imported MacroM registry.
//!
//! The pin's liftMacroM commits Macro.State only on success. In particular a
//! candidate's Unsupported/error state is discarded, while a successful macro's
//! scopes and traces survive subsequent tactic proof-state backtracking.

use super::lookup::EnvironmentMacroLookup;
use super::registrations::{
    MacroAttempt, MacroDispatch, MacroDispatchInvocation, MacroTreeLimits, MacroTreeUsage,
    RegisteredExpansion, RegisteredMacros,
};
use super::{MacroContext, MacroState};
use crate::Environment;
use fln_core::diag::ResourceReason;
use fln_core::name::Name;
use fln_core::outcome::{Inconclusive, InternalFault, Outcome, ResourceUsage};
use fln_elab::source::scope::SourceScope;
use fln_elab::tactic_macros::{TacticMacroError, TacticMacroExpander, TacticMacroExpansion};
use fln_syntax::source::SourceText;
use fln_syntax::tree::Syntax;
use fln_vm::interpreter::ExecutionUsage;
use std::sync::{Mutex, MutexGuard};

pub(crate) struct TacticReport {
    pub state: MacroState,
    pub attempts: Vec<MacroAttempt>,
    pub vm_usage: ExecutionUsage,
    pub tree_usage: MacroTreeUsage,
    closed: bool,
}

pub(crate) struct ImportedTactics {
    registry: RegisteredMacros,
    source: SourceText,
    context: MacroContext,
    limits: MacroTreeLimits,
    progress: Mutex<TacticReport>,
}

fn fault(message: &str) -> TacticMacroError {
    TacticMacroError::InternalFault(InternalFault::new("FL-INV-07", message))
}

fn usage_overflow() -> TacticMacroError {
    TacticMacroError::Inconclusive(Box::new(Inconclusive::dependency_unavailable(
        "imported tactic macro usage overflow",
    )))
}

fn stopped(at: &'static str, allowed: u64, observed: u64) -> TacticMacroError {
    TacticMacroError::Inconclusive(Box::new(
        Inconclusive::resource(ResourceUsage {
            reason: ResourceReason::ExecutionSteps,
            allowed,
            observed,
        })
        .with_progress(at),
    ))
}

impl ImportedTactics {
    pub(crate) fn new(
        registry: RegisteredMacros,
        source: SourceText,
        context: MacroContext,
        state: MacroState,
        limits: MacroTreeLimits,
    ) -> Self {
        Self {
            registry,
            source,
            context,
            limits,
            progress: Mutex::new(TacticReport {
                state,
                attempts: Vec::new(),
                vm_usage: ExecutionUsage {
                    steps: 0,
                    system_polls: 0,
                    peak_stack_depth: 0,
                },
                tree_usage: MacroTreeUsage::default(),
                closed: false,
            }),
        }
    }

    fn lock(&self) -> Result<MutexGuard<'_, TacticReport>, TacticMacroError> {
        self.progress
            .lock()
            .map_err(|_| fault("imported tactic macro state lock poisoned"))
    }

    pub(crate) fn take_report(&self) -> Result<TacticReport, TacticMacroError> {
        let mut progress = self.lock()?;
        if progress.closed {
            return Err(fault("imported tactic macro provider finalized twice"));
        }
        progress.closed = true;
        Ok(TacticReport {
            state: progress.state.clone(),
            attempts: std::mem::take(&mut progress.attempts),
            vm_usage: std::mem::replace(
                &mut progress.vm_usage,
                ExecutionUsage {
                    steps: 0,
                    system_polls: 0,
                    peak_stack_depth: 0,
                },
            ),
            tree_usage: std::mem::take(&mut progress.tree_usage),
            closed: true,
        })
    }

    fn remaining(&self, progress: &TacticReport) -> MacroTreeLimits {
        let mut limits = self.limits;
        limits.dispatch.max_attempts = limits
            .dispatch
            .max_attempts
            .saturating_sub(progress.attempts.len() as u64);
        limits.dispatch.execution.vm.max_steps = limits
            .dispatch
            .execution
            .vm
            .max_steps
            .saturating_sub(progress.vm_usage.steps);
        limits.max_visits = limits.max_visits.saturating_sub(progress.tree_usage.visits);
        limits.generation.max_nodes = limits
            .generation
            .max_nodes
            .saturating_sub(progress.tree_usage.generated_nodes);
        limits.generation.max_bytes = limits
            .generation
            .max_bytes
            .saturating_sub(progress.tree_usage.generated_bytes);
        limits
    }

    fn context(&self, depth: usize) -> Result<MacroContext, TacticMacroError> {
        let mut context = self.context.clone();
        let observed = context
            .current_recursion_depth
            .checked_add(depth as u64)
            .and_then(|depth| depth.checked_add(1))
            .ok_or_else(|| stopped("tactic macro recursion depth", u64::MAX - 1, u64::MAX))?;
        if observed > context.max_recursion_depth {
            return Err(TacticMacroError::Inconclusive(Box::new(
                Inconclusive::resource(ResourceUsage {
                    reason: ResourceReason::RecursionDepth {
                        limit: context.max_recursion_depth,
                    },
                    allowed: context.max_recursion_depth,
                    observed,
                })
                .with_progress("tactic macro recursion depth"),
            )));
        }
        context.current_recursion_depth = observed;
        Ok(context)
    }

    fn dispatch(
        &self,
        syntax: &Syntax,
        context: &MacroContext,
        candidate: Option<usize>,
        environment: &Environment,
        scope: &SourceScope,
        progress: &mut TacticReport,
    ) -> Result<RegisteredExpansion, TacticMacroError> {
        if progress.closed {
            return Err(TacticMacroError::Unsupported(
                "imported tactic provider belongs to a completed source command".into(),
            ));
        }
        let anonymous = Name::anonymous();
        let module = scope
            .source_module
            .as_ref()
            .or(scope.private_module.as_ref())
            .unwrap_or(&anonymous);
        let lookup = EnvironmentMacroLookup::new(
            environment,
            module,
            &scope.namespace,
            &scope.opened,
            &scope.explicit_opens,
        );
        let (report, tree) = self.registry.expand_runtime_root(
            syntax,
            MacroDispatchInvocation {
                source: &self.source,
                context,
                state: progress.state.clone(),
                lookup: Some(&lookup),
            },
            self.remaining(progress),
            candidate,
        );
        let MacroDispatch {
            outcome,
            mut attempts,
            completed_vm_usage,
        } = report;
        progress.vm_usage.steps = progress
            .vm_usage
            .steps
            .checked_add(completed_vm_usage.steps)
            .ok_or_else(usage_overflow)?;
        progress.vm_usage.system_polls = progress
            .vm_usage
            .system_polls
            .checked_add(completed_vm_usage.system_polls)
            .ok_or_else(usage_overflow)?;
        progress.vm_usage.peak_stack_depth = progress
            .vm_usage
            .peak_stack_depth
            .max(completed_vm_usage.peak_stack_depth);
        progress.tree_usage.visits = progress
            .tree_usage
            .visits
            .checked_add(tree.visits)
            .ok_or_else(usage_overflow)?;
        progress.tree_usage.generated_nodes = progress
            .tree_usage
            .generated_nodes
            .checked_add(tree.generated_nodes)
            .ok_or_else(usage_overflow)?;
        progress.tree_usage.generated_bytes = progress
            .tree_usage
            .generated_bytes
            .checked_add(tree.generated_bytes)
            .ok_or_else(usage_overflow)?;
        progress.attempts.try_reserve(attempts.len()).map_err(|_| {
            TacticMacroError::Inconclusive(Box::new(Inconclusive::dependency_unavailable(
                "imported tactic macro attempt allocation",
            )))
        })?;
        progress.attempts.append(&mut attempts);
        match outcome {
            Outcome::Complete(Ok(result)) => Ok(result),
            Outcome::Complete(Err(error)) => Err(TacticMacroError::Unsupported(error.to_string())),
            Outcome::Inconclusive(reason) => Err(TacticMacroError::Inconclusive(Box::new(reason))),
            Outcome::InternalFault(fault) => Err(TacticMacroError::InternalFault(fault)),
        }
    }
}

impl TacticMacroExpander for ImportedTactics {
    fn contains(&self, kind: &Name) -> bool {
        self.registry.declarations(kind).next().is_some()
    }

    fn enter_tactic(&self, depth: usize) -> Result<u64, TacticMacroError> {
        self.context(depth)?;
        let mut progress = self.lock()?;
        if progress.closed {
            return Err(TacticMacroError::Unsupported(
                "imported tactic provider belongs to a completed source command".into(),
            ));
        }
        if progress.tree_usage.visits >= self.limits.max_visits {
            return Err(stopped(
                "imported tactic visits",
                self.limits.max_visits,
                self.limits.max_visits.saturating_add(1),
            ));
        }
        progress.tree_usage.visits += 1;
        let current = progress.state.macro_scope;
        progress.state.macro_scope = current
            .checked_add(1)
            .ok_or_else(|| stopped("tactic macro scope counter", u64::MAX - 1, u64::MAX))?;
        Ok(current)
    }

    fn expand_tactic(
        &self,
        syntax: &Syntax,
        candidate: usize,
        macro_scope: u64,
        depth: usize,
        environment: &Environment,
        scope: &SourceScope,
    ) -> Result<TacticMacroExpansion, TacticMacroError> {
        let Some(no_fallback) = syntax
            .kind()
            .and_then(|kind| self.registry.tactic_candidate_no_fallback(kind, candidate))
        else {
            return Ok(TacticMacroExpansion::Exhausted);
        };
        let mut context = self.context(depth)?;
        context.current_macro_scope = macro_scope;
        let mut progress = self.lock()?;
        match self.dispatch(
            syntax,
            &context,
            Some(candidate),
            environment,
            scope,
            &mut progress,
        )? {
            RegisteredExpansion::Expanded { syntax, state, .. } => {
                progress.state = state;
                Ok(TacticMacroExpansion::Expanded {
                    syntax,
                    no_fallback,
                })
            }
            RegisteredExpansion::Unsupported { .. } => Ok(TacticMacroExpansion::Unsupported),
            RegisteredExpansion::Error {
                declaration,
                message,
                ..
            } => Ok(TacticMacroExpansion::Diagnostic {
                error: TacticMacroError::Diagnostic {
                    declaration,
                    message,
                },
                no_fallback,
            }),
        }
    }

    fn expand_term(
        &self,
        syntax: &Syntax,
        depth: usize,
        environment: &Environment,
        scope: &SourceScope,
    ) -> Result<Option<Syntax>, TacticMacroError> {
        let kind = match syntax {
            Syntax::Node { kind, .. } => kind.clone(),
            Syntax::Ident { .. } => Name::from_components(["ident"]),
            Syntax::Missing => Name::from_components(["missing"]),
            Syntax::Atom { val, .. } => {
                if val.len() > self.limits.dispatch.execution.syntax.max_bytes {
                    return Err(TacticMacroError::Unsupported(
                        "term atom exceeds macro syntax byte bound".into(),
                    ));
                }
                Name::str(Name::anonymous(), val)
            }
        };
        if !self.contains(&kind) {
            return Ok(None);
        }
        let context = self.context(depth)?;
        let mut progress = self.lock()?;
        match self.dispatch(syntax, &context, None, environment, scope, &mut progress)? {
            RegisteredExpansion::Expanded { syntax, state, .. } => {
                progress.state = state;
                Ok(Some(syntax))
            }
            RegisteredExpansion::Unsupported { state } => {
                progress.state = state;
                Ok(None)
            }
            RegisteredExpansion::Error {
                declaration,
                message,
                ..
            } => Err(TacticMacroError::Diagnostic {
                declaration,
                message,
            }),
        }
    }
}
