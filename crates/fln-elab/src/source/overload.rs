//! Overloaded identifiers (bead `fln-wh2j`): the pin's `elabAppAux` (vendored
//! `src/Lean/Elab/App.lean:2201-2219`, with `elabAppFnResolutions` at 1926-1945).
//!
//! When name resolution (`scope.rs`, the pin's `resolveGlobalName`) yields more than
//! one declaration for an identifier, the pin elaborates the application once per
//! interpretation against the expected type, each ending in `ensureHasType` because
//! the head is overloaded, and keeps those that succeed. Exactly one success is the
//! term; more than one is "Ambiguous term" with every interpretation listed; none is
//! "overloaded, errors". So under `open P`, with `foo : Nat` at the root and
//! `P.foo : Nat`, `def x : Nat := foo` is ambiguous, while with `P.foo : Bool` only
//! the root interpretation has type `Nat` and the pin accepts it.
//!
//! Each interpretation is elaborated here in a speculative copy of the context, from
//! the same syntax with its head written `_root_.<candidate>`, which names exactly
//! that declaration. The spent budget carries over from one copy to the next.
//!
//! An interpretation counts as a success only when it elaborates and its type is the
//! expected one: the trial has already run `coerce_expected` (this crate's
//! `ensureHasType`), so a coercion the environment provides is in place. Choosing
//! one interpretation also asserts that the pin rejects every other one. So another
//! interpretation is ruled out only on that definite evidence:
//! - it elaborated;
//! - its type and the expected type are closed (no metavariables, no free
//!   variables), and the kernel finds them not definitionally equal (the kernel's
//!   conversion is at least as permissive as the pin's `isDefEq`);
//! - the coercion classes were imported from the pin's library, so the coercion
//!   search that found nothing searched the pin's own instances.
//!
//! Every other non-success leaves the interpretation undetermined, and the identifier
//! is refused rather than resolved by guessing:
//! - an elaboration refusal;
//! - a type that is not closed;
//! - a mismatch on a FrankenLean seed, which stages coercion classes but not the
//!   pin's `Init` coercions, so it cannot rule out one the pin has.
//!
//! A resource stop or internal nonanswer propagates, as runtime exceptions escape
//! the pin's `observing`.
use super::*;

/// Nesting of overload trials: an overloaded argument of an overloaded application,
/// and so on. Each level runs a nested elaboration; deeper nesting is a resource stop.
pub(super) const MAX_OVERLOAD_DEPTH: u8 = 16;

impl Context {
    /// `elabAppAux` over the interpretations of an overloaded `head`, applied to
    /// `arguments` when it heads an application.
    pub(super) fn overloaded(
        &mut self,
        head: &Syntax,
        arguments: Option<&[Syntax]>,
        name: &Name,
        candidates: &[Name],
        expected: Option<&Expr>,
    ) -> Result<Typed, NatDefinitionElabError> {
        if self.overload_depth >= MAX_OVERLOAD_DEPTH {
            return Err(failure(SourceInferenceError::ResourceLimit));
        }
        let mut successes: Vec<(Name, Box<Context>, Typed)> = Vec::new();
        let mut failures: Vec<(Name, String)> = Vec::new();
        let mut undetermined: Option<Name> = None;
        for candidate in candidates {
            self.tick()?;
            let syntax = interpretation_syntax(head, arguments, candidate)?;
            let mut trial = Box::new(self.clone());
            trial.overload_depth += 1;
            let outcome = trial.interpretation(&syntax, expected);
            self.txn.budget.heartbeats_consumed = trial.txn.budget.heartbeats_consumed;
            match outcome? {
                Some(Ok(term)) => successes.push((candidate.clone(), trial, term)),
                Some(Err(reason)) => failures.push((candidate.clone(), reason)),
                None => {
                    undetermined.get_or_insert_with(|| candidate.clone());
                }
            }
        }
        if successes.len() > 1 {
            return Err(failure(SourceInferenceError::AmbiguousTerm {
                name: name.clone(),
                interpretations: successes
                    .into_iter()
                    .map(|(candidate, _, _)| candidate)
                    .collect(),
            }));
        }
        if let Some(candidate) = undetermined {
            return Err(failure(SourceInferenceError::OverloadUndetermined {
                name: name.clone(),
                candidate,
            }));
        }
        match successes.pop() {
            Some((_, trial, term)) => {
                let spent = self.txn.budget.heartbeats_consumed;
                let depth = self.overload_depth;
                *self = *trial;
                self.txn.budget.heartbeats_consumed = spent;
                self.overload_depth = depth;
                Ok(term)
            }
            None => Err(failure(SourceInferenceError::OverloadFailed {
                name: name.clone(),
                failures,
            })),
        }
    }

    /// One interpretation: `Some(Ok)` a success, `Some(Err)` a definite failure the
    /// pin's elaborator shares, `None` neither established nor ruled out.
    fn interpretation(
        &mut self,
        syntax: &Syntax,
        expected: Option<&Expr>,
    ) -> Result<Option<Result<Typed, String>>, NatDefinitionElabError> {
        let term = match self.term_prepared(syntax, expected.cloned()) {
            Ok(term) => term,
            Err(error) if !super::operators::probe_says_no(&error) => return Err(error),
            Err(_) => return Ok(None),
        };
        let Some(expected) = expected else {
            return Ok(Some(Ok(term)));
        };
        if self.defeq_guarded(&term.type_, expected)? {
            return Ok(Some(Ok(term)));
        }
        let actual = self.instantiate(&term.type_)?;
        let target = self.instantiate(expected)?;
        let closed = |e: &Expr| !(e.has_expr_mvar() || e.has_level_mvar() || e.has_fvar());
        if !closed(&actual) || !closed(&target) || !self.coercions_are_the_pins()? {
            return Ok(None);
        }
        if self.coercion_kernel_eq(actual, target)? {
            return Ok(Some(Ok(term)));
        }
        Ok(Some(Err("type mismatch".to_owned())))
    }
}

/// The interpretations of `head` when `error` is its own resolution refusing it as
/// ambiguous: the identifier the pin elaborates as overloaded, its candidates in the
/// order the pin tries them. Name resolution is the first thing elaborating an
/// identifier does, so nothing but budget has been spent when this error arises.
pub(super) fn ambiguous_head(
    error: &NatDefinitionElabError,
    head: &Syntax,
) -> Option<(Name, Vec<Name>)> {
    let Syntax::Ident { val, .. } = head else {
        return None;
    };
    match error {
        NatDefinitionElabError::Inference(SourceInferenceError::NameScope(
            scope::ScopeError::Ambiguous(name, candidates),
        )) if name == val => Some((name.clone(), candidates.clone())),
        _ => None,
    }
}

impl Context {
    /// Whether a coercion search here is the pin's own: the coercion classes came from
    /// the pin's library through an import (the imported-instance journal records
    /// them), so the instances searched are the pin's, plus the file's own. FrankenLean's
    /// seeds stage the classes without the pin's concrete coercions (no `Bool` to `Prop`,
    /// for one), so a search that finds nothing there says nothing about the pin.
    fn coercions_are_the_pins(&self) -> Result<bool, NatDefinitionElabError> {
        let class = Name::from_components(["CoeT"]);
        Ok(self.txn.env.contains(&class)
            && self
                .instance_registry()?
                .imported_class_parameters(&class)
                .is_some())
    }
}

/// `head` written `_root_.<candidate>`, applied to `arguments` when present.
fn interpretation_syntax(
    head: &Syntax,
    arguments: Option<&[Syntax]>,
    candidate: &Name,
) -> Result<Syntax, NatDefinitionElabError> {
    let Syntax::Ident { info, raw_val, .. } = head else {
        return Err(failure(SourceInferenceError::Scope));
    };
    let head = Syntax::Ident {
        info: *info,
        raw_val: *raw_val,
        val: Name::from_components(["_root_"]).append_core(candidate),
        preresolved: Vec::new(),
    };
    Ok(match arguments {
        Some(arguments) => Syntax::node(
            parser_kind(&["Term", "app"]),
            vec![
                head,
                Syntax::node(Name::from_components(["null"]), arguments.to_vec()),
            ],
        ),
        None => head,
    })
}
