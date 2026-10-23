//! Raw tactic traces are observational data, never proof authority.
//!
//! The pin's Term.SavedState.restore retains raw traces across backtracking.
//! A command-local shared log mirrors that rule without process-global state.
use super::*;
use std::sync::{Arc, Mutex};

const MAX_EVENTS: usize = 4096;
const MAX_GOALS: usize = 256;
const MAX_LOCALS: usize = 4096;
const MAX_MESSAGE_BYTES: usize = 16 * 1024 * 1024;

#[derive(Debug, Clone, PartialEq)]
pub struct TraceGoal {
    pub tag: Name,
    pub target: Expr,
    pub locals: LocalContext,
}

#[derive(Debug, Clone, PartialEq)]
pub enum TraceContent {
    Goals(Vec<TraceGoal>),
    Message(String),
}

#[derive(Debug, Clone, PartialEq)]
pub struct SourceTrace {
    /// Syntax byte offset relative to its command. Elaboration returns a
    /// normalized offset; the source engine maps it to the original buffer.
    pub at: usize,
    pub content: TraceContent,
    pub scope: SourceScope,
}

/// Observations accompany an untrusted candidate, never replace its checks.
pub struct ObservedDeclaration {
    pub candidate: ElaboratedDeclaration,
    pub traces: Vec<SourceTrace>,
}

/// The ordinary scoped definition elaborator with an explicit diagnostic owner.
/// Entry points returning only a declaration retain their refusal when a raw
/// trace is actually executed, rather than silently dropping its output.
pub fn elaborate_definition(
    syntax: &Syntax,
    environment: &Environment,
    kernel: Budget,
    scope: &SourceScope,
) -> Result<ObservedDeclaration, NatDefinitionElabError> {
    let scope = scope.for_declaration(syntax)?;
    let mut context = Context::scoped(environment, kernel, &scope);
    context.traces.enable();
    let declaration = definition_in_context(syntax, &mut context)?;
    let local_functions = context.lift_local_functions(&declaration)?;
    Ok(ObservedDeclaration {
        candidate: ElaboratedDeclaration {
            declaration,
            native_axioms: Vec::new(),
            local_functions,
            irreducible: context.well_founded_definition,
            noncomputable: context.noncomputable_definition,
        },
        traces: context.traces.collect()?,
    })
}

/// Examples share definition elaboration but their successor remains scratch-only.
pub fn elaborate_example(
    syntax: &Syntax,
    name: Name,
    environment: &Environment,
    kernel: Budget,
    scope: &SourceScope,
) -> Result<(Declaration, Vec<SourceTrace>), NatDefinitionElabError> {
    let mut context = Context::scoped(environment, kernel, scope);
    context.traces.enable();
    let declaration = scope::example_in_context(syntax, name, &mut context)?;
    Ok((declaration, context.traces.collect()?))
}

#[derive(Clone, Default)]
pub(super) struct TraceLog(Option<Arc<Mutex<RetainedTraces>>>);

#[derive(Default)]
struct RetainedTraces {
    events: Vec<SourceTrace>,
    units: usize,
    message_bytes: usize,
}

impl TraceLog {
    pub fn enabled(&self) -> bool {
        self.0.is_some()
    }
    pub fn enable(&mut self) {
        self.0 = Some(Arc::new(Mutex::new(RetainedTraces::default())));
    }
    pub fn collect(&self) -> Result<Vec<SourceTrace>, NatDefinitionElabError> {
        self.0.as_ref().map_or_else(
            || Ok(Vec::new()),
            |log| {
                log.lock()
                    .map(|log| log.events.clone())
                    .map_err(|_| failure(SourceInferenceError::Scope))
            },
        )
    }
    fn append(&self, event: SourceTrace) -> Result<(), NatDefinitionElabError> {
        let Some(log) = &self.0 else {
            return Err(failure(SourceInferenceError::Tactic(
                tactics::TacticError::UnsupportedTactic(parser_kind(&["Tactic", "traceState"])),
            )));
        };
        let mut log = log
            .lock()
            .map_err(|_| failure(SourceInferenceError::Scope))?;
        let (incoming, bytes) = match &event.content {
            TraceContent::Goals(goals) => {
                (goals.iter().map(|g| g.locals.len() + 1).sum::<usize>(), 0)
            }
            TraceContent::Message(message) => (0, message.len()),
        };
        if log.events.len() >= MAX_EVENTS
            || incoming.saturating_add(log.units) > 65_536
            || bytes.saturating_add(log.message_bytes) > MAX_MESSAGE_BYTES
        {
            return Err(failure(SourceInferenceError::ResourceLimit));
        }
        log.units += incoming;
        log.message_bytes += bytes;
        log.events.push(event);
        Ok(())
    }
}

pub(super) fn append_tag(parent: &Name, child: &Name) -> Name {
    let mut parts = Vec::new();
    let mut current = child.clone();
    while !current.is_anonymous() {
        parts.push(current.clone());
        current = current.parent();
    }
    parts
        .into_iter()
        .rev()
        .fold(parent.clone(), |tag, part| match part.leaf_view() {
            LeafView::Str(s) => Name::str(tag, s),
            LeafView::Num(n) => Name::num(tag, n),
            LeafView::Anonymous => tag,
        })
}

impl Context {
    /// Remember the source stem for an inaccessible introduction. These names
    /// are display-only: tactic name resolution still uses the original local.
    pub(super) fn trace_introduced_name(&mut self, id: &FVarId, name: &Name, binder: &Name) {
        if name.parent() == Name::from_components(["_fln_source"]) {
            self.trace_hygienic_name(id, binder);
        }
    }

    /// Show a local as its binder's name made inaccessible (`n✝`, `n_ih✝`): an unnamed
    /// elimination field, as the pin names it after the minor premise's binder.
    pub(super) fn trace_hygienic_name(&mut self, id: &FVarId, binder: &Name) {
        if self.traces.enabled() {
            // An arrow's binder is already hygienic (`a✝`); the stem is the name under its
            // scopes, as the pin's `mkFreshBinderNameForTactic` reads it.
            let binder = binder.erase_macro_scopes();
            let stem = if binder.is_anonymous() {
                Name::from_components(["a"])
            } else {
                binder
            };
            // The existing printer uses the normal Name hygiene grammar, with
            // the exact generated identity as the scope (not a shared counter).
            let display = Name::num(
                Name::str(Name::str(stem, "_@"), "_hyg"),
                match id.0.leaf_view() {
                    LeafView::Num(n) => n,
                    _ => 0,
                },
            );
            self.trace_local_names.insert(id.clone(), display);
        }
    }

    /// Literal trace messages do not inspect or elaborate a goal. In particular
    /// they also run with no remaining goals and inside failed alternatives.
    pub(super) fn record_message_trace(
        &mut self,
        instruction: &Syntax,
    ) -> Result<(), NatDefinitionElabError> {
        self.require_declared_tactic(&["Lean", "Parser", "Tactic", "traceMessage"])?;
        let args = expect_node(
            instruction,
            &parser_kind(&["Tactic", "traceMessage"]),
            2,
            "trace message",
        )?;
        expect_atom(&args[0], "trace", "trace message keyword")?;
        let literal = expect_node(&args[1], &Name::from_components(["str"]), 1, "trace string")?;
        let Syntax::Atom { val: spelling, .. } = &literal[0] else {
            return Err(failure(SourceInferenceError::Tactic(
                tactics::TacticError::MalformedScript,
            )));
        };
        if spelling.len() > MAX_MESSAGE_BYTES {
            return Err(failure(SourceInferenceError::ResourceLimit));
        }
        for _ in spelling.as_bytes().chunks(1024) {
            self.tick()?;
        }
        let Literal::Str(message) = decode_string(spelling)? else {
            return Err(failure(SourceInferenceError::Tactic(
                tactics::TacticError::MalformedScript,
            )));
        };
        self.traces.append(SourceTrace {
            at: args[0].info().pos(true).map_or(0, |p| p.0),
            content: TraceContent::Message(message),
            scope: self.source_scope.clone(),
        })
    }

    pub(super) fn record_goal_trace(
        &mut self,
        instruction: &Syntax,
        goals: &[tactics::ProofGoal],
    ) -> Result<(), NatDefinitionElabError> {
        self.require_declared_tactic(&["Lean", "Parser", "Tactic", "traceState"])?;
        let args = expect_node(
            instruction,
            &parser_kind(&["Tactic", "traceState"]),
            1,
            "trace_state",
        )?;
        expect_atom(&args[0], "trace_state", "trace_state keyword")?;
        if goals.len() > MAX_GOALS {
            return Err(failure(SourceInferenceError::ResourceLimit));
        }
        let mut observed = Vec::new();
        for goal in goals {
            self.tick()?;
            if goal.lctx.len() > MAX_LOCALS {
                return Err(failure(SourceInferenceError::ResourceLimit));
            }
            let mut locals = LocalContext::new();
            for local in goal.lctx.decls() {
                self.tick()?;
                if self.is_matrix_hypothesis(local) {
                    continue;
                }
                let user_name = self
                    .trace_local_names
                    .get(&local.id)
                    .unwrap_or(&local.user_name)
                    .clone();
                let type_ = self.instantiate(&local.type_)?;
                if let Some(value) = &local.value {
                    let value = self.instantiate(value)?;
                    locals.add_let(local.id.clone(), user_name, type_, value);
                } else {
                    locals.add_param(local.id.clone(), user_name, type_, local.binder_info);
                }
            }
            observed.push(TraceGoal {
                tag: self
                    .goal_tags
                    .get(&goal.id)
                    .cloned()
                    .unwrap_or_else(Name::anonymous),
                target: self.instantiate(&goal.target)?,
                locals,
            });
        }
        self.traces.append(SourceTrace {
            at: args[0].info().pos(true).map_or(0, |p| p.0),
            content: TraceContent::Goals(observed),
            scope: self.source_scope.clone(),
        })
    }
}

/// A caller with no output channel must refuse, not lose an observable trace.
pub fn contains_trace(syntax: &Syntax) -> bool {
    let mut pending = vec![syntax];
    while let Some(syntax) = pending.pop() {
        if let Syntax::Node { kind, args, .. } = syntax {
            if kind == &parser_kind(&["Tactic", "traceState"])
                || kind == &parser_kind(&["Tactic", "traceMessage"])
            {
                return true;
            }
            pending.extend(args);
        }
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;
    fn event() -> SourceTrace {
        SourceTrace {
            at: 0,
            content: TraceContent::Goals(Vec::new()),
            scope: SourceScope::default(),
        }
    }
    #[test]
    fn snapshots_share_only_raw_traces_and_keep_a_non_refundable_bound() {
        let mut log = TraceLog::default();
        log.enable();
        let prior = log.clone();
        log.append(event()).unwrap();
        assert_eq!(prior.collect().unwrap().len(), 1);
        for _ in 1..MAX_EVENTS {
            prior.append(event()).unwrap();
        }
        assert!(matches!(
            log.append(event()),
            Err(NatDefinitionElabError::Inference(
                SourceInferenceError::ResourceLimit
            ))
        ));
        assert_eq!(log.collect().unwrap().len(), MAX_EVENTS);
        let mut independent = TraceLog::default();
        independent.enable();
        assert!(independent.collect().unwrap().is_empty());
    }
    #[test]
    fn a_missing_diagnostic_channel_does_not_silently_ignore_a_trace() {
        assert!(matches!(
            TraceLog::default().append(event()),
            Err(NatDefinitionElabError::Inference(
                SourceInferenceError::Tactic(tactics::TacticError::UnsupportedTactic(_))
            ))
        ));
    }
    #[test]
    fn literal_trace_capacity_is_shared_and_failure_atomic() {
        let mut log = TraceLog::default();
        log.enable();
        let snapshot = log.clone();
        for _ in 0..4 {
            let mut message = event();
            message.content = TraceContent::Message("x".repeat(MAX_MESSAGE_BYTES / 4));
            log.append(message).unwrap();
        }
        let mut extra = event();
        extra.content = TraceContent::Message("x".into());
        assert!(matches!(
            snapshot.append(extra),
            Err(NatDefinitionElabError::Inference(
                SourceInferenceError::ResourceLimit
            ))
        ));
        assert_eq!(snapshot.collect().unwrap().len(), 4);
        let mut independent = TraceLog::default();
        independent.enable();
        independent.append(event()).unwrap();
        assert_eq!(independent.collect().unwrap().len(), 1);
    }
}
