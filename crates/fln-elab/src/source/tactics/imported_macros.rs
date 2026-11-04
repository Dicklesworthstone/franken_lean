//! Runtime imported-macro alternatives and the owned Syntax frame boundary.
//!
//! The surrounding worklist borrows source Syntax. An expansion instead lives
//! in a nested evaluator call, which may return only goals and closing terms.
//! No reference into the generated tree escapes that call, and a successful
//! tactic may leave any number of goals for the original source continuation.

use super::*;
use crate::tactic_macros::{TacticMacroError, TacticMacroExpansion};

// Each owned expansion runs a native evaluator on the host stack. Keep this
// independent of Lean's reader depth and fail typed before exhausting it.
const MAX_OWNED_FRAMES: usize = 8;

#[derive(Clone)]
pub(in crate::source) enum FrontierWork {
    Goal(ProofGoal),
    Close(ProofGoal, Expr),
}

pub(in crate::source) enum TacticCompletion {
    Frontier(Vec<FrontierWork>),
    NoElaborator,
}

#[derive(Clone, Copy)]
pub(super) struct OwnedFrame<'a> {
    /// The root being tried as a native elaborator after its macro candidates.
    /// A nested tactic still dispatches its own macros normally.
    pub builtin: Option<&'a Syntax>,
    pub entered: bool,
}

pub(in crate::source) fn macro_error(error: TacticMacroError) -> NatDefinitionElabError {
    failure(SourceInferenceError::TacticMacro(error))
}

fn frame_limit() -> NatDefinitionElabError {
    macro_error(TacticMacroError::Inconclusive(Box::new(
        fln_core::outcome::Inconclusive::resource(fln_core::outcome::ResourceUsage {
            reason: fln_core::diag::ResourceReason::RecursionDepth {
                limit: MAX_OWNED_FRAMES as u64,
            },
            allowed: MAX_OWNED_FRAMES as u64,
            observed: MAX_OWNED_FRAMES as u64 + 1,
        })
        .with_progress("imported macro owned evaluator depth"),
    )))
}

impl ProofState<'_> {
    pub(super) fn builtin_root(&self, instruction: &Syntax) -> bool {
        self.owned_frame
            .and_then(|frame| frame.builtin)
            .is_some_and(|root| std::ptr::eq(root, instruction))
    }

    /// Only the currently visible, syntax-free frontier moves into an owned
    /// frame. Scripted branches and suspended controls stay in their caller.
    fn take_frontier(&mut self) -> Vec<FrontierWork> {
        let boundary = self
            .work
            .iter()
            .rposition(|work| !matches!(work, Work::Goal(_) | Work::Close(..)))
            .map_or(0, |position| position + 1);
        self.work
            .split_off(boundary)
            .into_iter()
            .map(|work| match work {
                Work::Goal(goal) => FrontierWork::Goal(goal),
                Work::Close(goal, term) => FrontierWork::Close(goal, term),
                _ => unreachable!("frontier boundary excludes borrowed work"),
            })
            .collect()
    }

    fn put_frontier(&mut self, frontier: Vec<FrontierWork>) {
        self.work
            .extend(frontier.into_iter().map(|work| match work {
                FrontierWork::Goal(goal) => Work::Goal(goal),
                FrontierWork::Close(goal, term) => Work::Close(goal, term),
            }));
    }

    pub(super) fn open_frontier(&mut self, goal: &ProofGoal) -> Option<TacticCompletion> {
        if self.owned_frame.is_none()
            || !self
                .work
                .iter()
                .all(|work| matches!(work, Work::Goal(_) | Work::Close(..)))
        {
            return None;
        }
        self.work.push(Work::Goal(goal.clone()));
        Some(TacticCompletion::Frontier(self.take_frontier()))
    }
}

impl Context {
    /// Same non-refunded work and auxiliary-name boundary as tactic first/try.
    /// The provider is shared and retains macro scopes, traces and VM usage.
    fn restore_macro_attempt(&mut self, checkpoint: &Context) {
        let spent = self.txn.budget.heartbeats_consumed;
        let auxiliary = self.aux_names.take();
        *self = checkpoint.clone();
        self.txn.budget.heartbeats_consumed = spent;
        self.aux_names = auxiliary;
    }

    fn run_owned_tactic(
        &mut self,
        syntax: &Syntax,
        original: &ProofState<'_>,
        frontier: &[FrontierWork],
        builtin: bool,
    ) -> Result<TacticCompletion, NatDefinitionElabError> {
        if self.tactic_macro_depth >= MAX_OWNED_FRAMES {
            return Err(frame_limit());
        }
        let prepared;
        let syntax = if builtin {
            syntax
        } else {
            self.check_preresolved_syntax(syntax)?;
            prepared = self.lower_pattern_matrices(syntax)?;
            &prepared
        };
        let mut proof = ProofState {
            extent: original.extent.clone(),
            saved: original.saved.clone(),
            target: original.target.clone(),
            root: original.root.clone(),
            instructions: vec![syntax],
            cursor: 0,
            work: Vec::new(),
            controls: Vec::new(),
            owned_frame: Some(OwnedFrame {
                builtin: builtin.then_some(syntax),
                entered: false,
            }),
        };
        proof.put_frontier(frontier.to_vec());
        let depth = self.tactic_macro_depth;
        let terms = self.tactic_macro_terms;
        let attempts = self.attempt_depth;
        let options = self.txn.options.clone();
        let implicit = self.no_implicit_lambda_types.len();
        let pending_arguments = self.pending_source_arguments;
        let saved_lctx = self.txn.lctx.clone();
        self.tactic_macro_depth += 1;
        self.tactic_macro_terms += 1;
        // The expansion is provisional until all of this candidate succeeds.
        self.attempt_depth += 1;
        let result = self.term_prepared_scoped(syntax, None, Some(proof), None, true);
        self.tactic_macro_depth = depth;
        self.tactic_macro_terms = terms;
        self.attempt_depth = attempts;
        self.txn.options = options;
        self.no_implicit_lambda_types.truncate(implicit);
        self.pending_source_arguments = pending_arguments;
        if result.is_ok() {
            self.txn.lctx = saved_lctx;
        }
        match result? {
            super::super::TermResult::Tactic(result) => Ok(result),
            super::super::TermResult::Term(_) => Err(failure(SourceInferenceError::Scope)),
        }
    }

    /// Called at every instruction boundary, including a body of first/try or
    /// all_goals and an instruction with no goals. Native fallback runs in its
    /// own frame so a failed macro expansion cannot consume the continuation.
    pub(super) fn imported_tactic<'a>(
        &mut self,
        proof: &mut ProofState<'a>,
        instruction: &'a Syntax,
    ) -> Result<bool, NatDefinitionElabError> {
        if let Some(frame) = &mut proof.owned_frame
            && !frame.entered
        {
            frame.entered = true;
            if frame
                .builtin
                .is_some_and(|root| std::ptr::eq(root, instruction))
            {
                return Ok(false);
            }
        }
        let Some(provider) = self.source_scope.tactic_macros.clone() else {
            return Ok(false);
        };
        let macro_scope = provider
            .0
            .enter_tactic(self.tactic_macro_depth)
            .map_err(macro_error)?;
        // evalTactic treats a null node as a sequence before consulting macros.
        if let Syntax::Node { kind, args, .. } = instruction
            && kind == &Name::from_components(["null"])
        {
            proof.cursor += 1;
            if !args.is_empty() {
                self.start_macro_scope(proof, args.iter().collect())?;
            }
            return Ok(true);
        }
        if matches!(instruction, Syntax::Missing) {
            proof.cursor += 1;
            return Ok(true);
        }
        let Some(kind) = instruction.kind() else {
            return Ok(false);
        };
        if !provider.0.contains(kind) {
            return Ok(false);
        }
        let frontier = proof.take_frontier();
        let checkpoint = self.clone();
        let mut last_failure = None;
        let mut candidate = 0usize;
        loop {
            self.tick()?;
            let expansion = provider
                .0
                .expand_tactic(
                    instruction,
                    candidate,
                    macro_scope,
                    self.tactic_macro_depth,
                    &self.txn.env,
                    &self.source_scope,
                )
                .map_err(macro_error)?;
            candidate = candidate.checked_add(1).ok_or_else(frame_limit)?;
            let (problem, no_fallback) = match expansion {
                TacticMacroExpansion::Exhausted => break,
                TacticMacroExpansion::Unsupported => continue,
                TacticMacroExpansion::Diagnostic { error, no_fallback } => {
                    (macro_error(error), no_fallback)
                }
                TacticMacroExpansion::Expanded {
                    syntax,
                    no_fallback,
                } => match self.run_owned_tactic(&syntax, proof, &frontier, false) {
                    Ok(TacticCompletion::Frontier(frontier)) => {
                        proof.put_frontier(frontier);
                        proof.cursor += 1;
                        return Ok(true);
                    }
                    Ok(TacticCompletion::NoElaborator) => {
                        return Err(failure(SourceInferenceError::Scope));
                    }
                    Err(problem) => (problem, no_fallback),
                },
            };
            if no_fallback || !backtrack::recoverable(&problem) {
                return Err(problem);
            }
            last_failure = Some((problem, Box::new(self.clone())));
            self.restore_macro_attempt(&checkpoint);
        }
        match self.run_owned_tactic(instruction, proof, &frontier, true) {
            Ok(TacticCompletion::Frontier(frontier)) => {
                proof.put_frontier(frontier);
                proof.cursor += 1;
                Ok(true)
            }
            Ok(TacticCompletion::NoElaborator) => {
                if let Some((problem, failed)) = last_failure {
                    self.restore_macro_attempt(&failed);
                    Err(problem)
                } else {
                    Err(macro_error(TacticMacroError::Diagnostic {
                        declaration: kind.clone(),
                        message: "unexpected tactic syntax".into(),
                    }))
                }
            }
            Err(problem) => Err(problem),
        }
    }

    pub(in crate::source) fn imported_tactic_term(
        &mut self,
        syntax: &Syntax,
        expected: Option<Expr>,
        finish: bool,
    ) -> Result<Option<Typed>, NatDefinitionElabError> {
        // The source pass expands nodes, but deliberately leaves atoms and
        // identifiers for actual term positions. In particular, a declaration
        // name or binder must never be rewritten by an `ident` registration.
        // Generated terms have not passed through that source pass, so their
        // nodes must also dispatch here. Missing syntax is handled directly by
        // the term elaborator, as in the pin's elabTermAux.
        if matches!(syntax, Syntax::Missing)
            || (self.tactic_macro_terms == 0 && matches!(syntax, Syntax::Node { .. }))
        {
            return Ok(None);
        }
        let Some(provider) = self.source_scope.tactic_macros.clone() else {
            return Ok(None);
        };
        let Some(expanded) = provider
            .0
            .expand_term(
                syntax,
                self.tactic_macro_depth,
                &self.txn.env,
                &self.source_scope,
            )
            .map_err(macro_error)?
        else {
            return Ok(None);
        };
        if self.tactic_macro_depth >= MAX_OWNED_FRAMES {
            return Err(frame_limit());
        }
        self.check_preresolved_syntax(&expanded)?;
        if let Some(expected) = &expected {
            self.check_application_typing(&expanded, expected)?;
        }
        let expanded = self.lower_pattern_matrices(&expanded)?;
        let depth = self.tactic_macro_depth;
        let terms = self.tactic_macro_terms;
        let options = self.txn.options.clone();
        let implicit = self.no_implicit_lambda_types.len();
        let pending_arguments = self.pending_source_arguments;
        self.tactic_macro_depth += 1;
        self.tactic_macro_terms += 1;
        let result = self.term_prepared_scoped(&expanded, expected, None, None, finish);
        self.tactic_macro_depth = depth;
        self.tactic_macro_terms = terms;
        self.txn.options = options;
        self.no_implicit_lambda_types.truncate(implicit);
        self.pending_source_arguments = pending_arguments;
        match result? {
            super::super::TermResult::Term(term) => Ok(Some(term)),
            super::super::TermResult::Tactic(_) => Err(failure(SourceInferenceError::Scope)),
        }
    }
}
