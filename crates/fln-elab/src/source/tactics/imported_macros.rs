//! Runtime imported-macro alternatives and the owned Syntax frame boundary.
//!
//! The surrounding worklist borrows source Syntax. An expansion instead lives
//! in a nested evaluator call, which may return only goals and closing terms.
//! No reference into the generated tree escapes that call, and a successful
//! tactic may leave any number of goals for the original source continuation.

use super::*;
use crate::tactic_macros::{TacticMacroError, TacticMacroExpansion};

// Nested owned evaluators retain a bounded reader depth. Consecutive root
// expansions use heap frames before entering the term evaluator, so a cycle
// reaches this typed limit without consuming a native evaluator stack per step.
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

fn prepared_pattern_literal(syntax: &Syntax) -> bool {
    syntax.kind().is_some_and(|kind| {
        matches!(
            kind.leaf_view(),
            fln_core::name::LeafView::Str("flnPreparedPatternLiteral")
        ) && *kind == parser_kind(&["Term", "flnPreparedPatternLiteral"])
    })
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
        let result = (|| {
            // Patterns in a generated tactic belong to this owned expansion
            // before the tactic worklist starts visiting its terms.
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
            self.term_prepared_scoped(syntax, None, Some(proof), None, true)
        })();
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
        let invocation = match self.source_scope.tactic_macros.clone() {
            Some(provider) => {
                let scope = provider
                    .0
                    .enter_tactic(self.tactic_macro_depth)
                    .map_err(macro_error)?;
                Some((provider, scope))
            }
            None => None,
        };
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
        let Some((provider, macro_scope)) = invocation else {
            return Ok(false);
        };
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
        if prepared_pattern_literal(syntax) {
            let prepared_kind = parser_kind(&["Term", "flnPreparedPatternLiteral"]);
            let parts = expect_node(syntax, &prepared_kind, 1, "prepared pattern literal")?;
            let literal = &parts[0];
            if !literal.kind().is_some_and(|kind| {
                ["num", "str", "char"]
                    .iter()
                    .any(|name| *kind == Name::from_components([*name]))
            }) {
                return Err(NatDefinitionElabError::UnexpectedSyntax {
                    expected: "prepared pattern literal",
                });
            }
            // The matrix has already decoded this value, including any source
            // macro expansion. Its comparison operand must retain that value;
            // internal predecessors must not become new user macro inputs.
            // Only builtin literal syntax can cross this boundary, and it
            // still goes through ordinary elaboration and kernel checking.
            let provider = self.source_scope.tactic_macros.take();
            let result = self.term_prepared_scoped(literal, expected, None, None, finish);
            self.source_scope.tactic_macros = provider;
            return match result? {
                super::super::TermResult::Term(term) => Ok(Some(term)),
                super::super::TermResult::Tactic(_) => Err(failure(SourceInferenceError::Scope)),
            };
        }
        let Some(provider) = self.source_scope.tactic_macros.clone() else {
            return Ok(None);
        };
        // The source pass expands compound nodes, but deliberately leaves
        // literal nodes and identifiers for actual term positions. A binder,
        // universe level or projection index must never be rewritten here.
        // Generated terms have not passed through that source pass, so their
        // nodes must also dispatch here. Missing syntax is handled directly by
        // the term elaborator, as in the pin's elabTermAux.
        if matches!(syntax, Syntax::Missing)
            || (self.tactic_macro_terms == 0
                && matches!(syntax, Syntax::Node { kind, .. }
                    if !fln_parse::extensions::is_atomic_macro_kind(kind)))
        {
            return Ok(None);
        }
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
        struct TermFrame {
            // A box keeps every observation address stable while the frame
            // vector grows and earlier root expansions remain live.
            syntax: Box<Syntax>,
            check: Option<super::super::pattern_typing::ApplicationCheck>,
            observation: Option<usize>,
            caller_locals: Option<LocalContext>,
            depth: usize,
            terms: usize,
            options: KVMap,
            implicit: usize,
            pending_arguments: bool,
            observations: usize,
        }

        let depth = self.tactic_macro_depth;
        let terms = self.tactic_macro_terms;
        let options = self.txn.options.clone();
        let implicit = self.no_implicit_lambda_types.len();
        let pending_arguments = self.pending_source_arguments;
        let observations = self.application_syntax.depth();
        let result = (|| {
            let mut frames: Vec<TermFrame> = Vec::new();
            let mut expanded = expanded;
            let mut caller_locals = None;
            let term = loop {
                if self.tactic_macro_depth >= MAX_OWNED_FRAMES {
                    return Err(frame_limit());
                }
                let depth = self.tactic_macro_depth;
                let terms = self.tactic_macro_terms;
                let options = self.txn.options.clone();
                let implicit = self.no_implicit_lambda_types.len();
                let pending_arguments = self.pending_source_arguments;
                let observations = self.application_syntax.depth();
                self.tactic_macro_depth += 1;
                self.tactic_macro_terms += 1;
                // Pattern macros belong to this root's reader depth, just as
                // they did when each root used a nested evaluator call.
                self.check_preresolved_syntax(&expanded)?;
                let check = expected
                    .as_ref()
                    .map(|expected| self.begin_application_typing(&expanded, expected))
                    .transpose()?
                    .flatten();
                let prepared = Box::new(match self.lower_pattern_matrices(&expanded)? {
                    std::borrow::Cow::Borrowed(_) => expanded,
                    std::borrow::Cow::Owned(prepared) => prepared,
                });
                if let Some(check) = &check {
                    self.bind_application_typing(&prepared, check)?;
                }
                let source = frames.last().map_or(syntax, |frame| &*frame.syntax);
                let observation = self.begin_macro_application_observation(source, &prepared)?;
                frames.push(TermFrame {
                    syntax: prepared,
                    check,
                    observation,
                    caller_locals,
                    depth,
                    terms,
                    options,
                    implicit,
                    pending_arguments,
                    observations,
                });
                let root = &*frames.last().expect("owned expansion frame").syntax;
                if prepared_pattern_literal(root) {
                    break self
                        .term_prepared_scoped(root, expected.clone(), None, None, finish)
                        .and_then(super::super::TermResult::term)?;
                }
                caller_locals = self.observes_term(root).then(|| self.txn.lctx.clone());
                let next = if matches!(root, Syntax::Missing) {
                    None
                } else {
                    provider
                        .0
                        .expand_term(
                            root,
                            self.tactic_macro_depth,
                            &self.txn.env,
                            &self.source_scope,
                        )
                        .map_err(macro_error)?
                };
                if let Some(next) = next {
                    expanded = next;
                    continue;
                }
                // The terminal lookup has already run once. Starting with an
                // Elaborate task preserves that result while descendants keep
                // their ordinary dispatch, expected types and postponement.
                break self
                    .term_prepared_expansion(root, expected.clone(), finish)
                    .and_then(super::super::TermResult::term)?;
            };
            while let Some(frame) = frames.pop() {
                let source = frames.last().map_or(syntax, |frame| &*frame.syntax);
                if let Some(observation) = frame.observation {
                    self.finish_macro_application_observation(source, &frame.syntax, observation)?;
                }
                if let Some(check) = frame.check {
                    self.finish_application_typing(&frame.syntax, check)?;
                }
                self.application_syntax.truncate(frame.observations);
                self.tactic_macro_depth = frame.depth;
                self.tactic_macro_terms = frame.terms;
                self.txn.options = frame.options;
                self.no_implicit_lambda_types.truncate(frame.implicit);
                self.pending_source_arguments = frame.pending_arguments;
                if let Some(locals) = frame.caller_locals {
                    self.observe_term(source, term.clone(), locals)?;
                }
            }
            Ok::<_, NatDefinitionElabError>(term)
        })();
        self.application_syntax.truncate(observations);
        self.tactic_macro_depth = depth;
        self.tactic_macro_terms = terms;
        self.txn.options = options;
        self.no_implicit_lambda_types.truncate(implicit);
        self.pending_source_arguments = pending_arguments;
        result.map(Some)
    }
}
