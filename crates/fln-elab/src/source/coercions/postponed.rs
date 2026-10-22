//! Coercions the pin postpones. `mkCoe` asks for a `CoeT` dictionary with the
//! value as it stands; when that search is stuck on an open metavariable (a
//! numeral whose type only a default instance fixes, an operator whose
//! instance is not synthesized yet) it returns `.undef` and registers a `.coe`
//! synthetic metavariable instead of failing (Lean/Elab/Term.lean). That is
//! how `#guard 2 = 1 + 1` and `xs.filter (· > 1)` reach `decPropToBool`.
//!
//! Only a mismatch that is otherwise refused here (a rigid one) is postponed,
//! so no term that elaborated before changes. A placeholder of the expected
//! type stands for the coerced value; instance synthesis retries the
//! coercion, and its final pass refuses what remains exactly as the
//! mismatch would have been refused when it was found.
use super::*;
use crate::lctx::LocalContext;

#[derive(Clone)]
pub(in crate::source) struct PostponedCoercion {
    hole: Expr,
    term: Typed,
    expected: Expr,
    lctx: LocalContext,
}

impl Context {
    /// Postpone the value coercion (`CoeT`) of `term` to `expected` when its
    /// value is still open and the mismatch is rigid. A sort target is a
    /// `CoeSort` question and is never postponed. None: refuse it now.
    ///
    /// Not inside an overload trial: there the pin keeps a delayed coercion
    /// only as a sole success, discarding it among several when it stays
    /// pending (`getSuccesses`, Lean/Elab/App.lean:2141). That is not modeled,
    /// and an interpretation that postponed would read as a success where it
    /// used to be ruled out by its type mismatch.
    pub(super) fn postpone_coercion(
        &mut self,
        term: &Typed,
        expected: &Expr,
    ) -> Result<Option<Typed>, NatDefinitionElabError> {
        if self.overload_depth > 0
            || !self.instantiate(&term.value)?.has_expr_mvar()
            || matches!(self.whnf(expected)?.node(), ExprNode::Sort { .. })
            || self.rigid_type_mismatch(&term.type_, expected)?.is_none()
        {
            return Ok(None);
        }
        let hole = self.hole(expected.clone())?;
        self.postponed_coercions.push(PostponedCoercion {
            hole: hole.clone(),
            term: term.clone(),
            expected: expected.clone(),
            lctx: self.txn.lctx.clone(),
        });
        Ok(Some(Typed {
            value: hole,
            type_: expected.clone(),
        }))
    }

    /// Before a `fun` or `∀` closes over `locals`, give each postponed coercion's hole that `body`
    /// holds, and whose context holds one of them, the value `?n x₁ … xₖ`, with `?n` outside the
    /// binders, in `outer`: the pin's `elimMVarDeps` (`MetavarContext.elimMVar`) for a natural
    /// metavariable. The coercion resumed later then solves `?n` as a pattern
    /// (`?n a b =?= decide (a < b)`), and its value stays under the binders. True when a hole was
    /// assigned, so the caller instantiates `body` again.
    pub(in crate::source) fn capture_bound_coercions(
        &mut self,
        locals: &[LocalDecl],
        outer: &LocalContext,
        body: &Typed,
    ) -> Result<bool, NatDefinitionElabError> {
        if locals.is_empty() || self.postponed_coercions.is_empty() {
            return Ok(false);
        }
        let mut present = self.txn.mvars.collect_mvars(&body.value);
        present.extend(self.txn.mvars.collect_mvars(&body.type_));
        let holes: Vec<Expr> = self
            .postponed_coercions
            .iter()
            .map(|record| record.hole.clone())
            .collect();
        let mut assigned = false;
        for hole in holes {
            self.tick()?;
            let ExprNode::MVar { id } = hole.node() else {
                continue;
            };
            if !present.contains(id) {
                continue;
            }
            let declaration = self
                .txn
                .mvars
                .get_decl(id)
                .cloned()
                .ok_or_else(|| failure(SourceInferenceError::Scope))?;
            let captured: Vec<LocalDecl> = locals
                .iter()
                .filter(|local| declaration.lctx.find(&local.id).is_some())
                .cloned()
                .collect();
            if captured.is_empty() {
                continue;
            }
            let type_ = self.instantiate(&declaration.type_)?;
            let type_ = self.forall_captured(&captured, type_)?;
            let name = self.fresh_name()?;
            let abstracted = MVarId(name.clone());
            self.txn.mvars.declare(
                abstracted.clone(),
                name,
                type_,
                outer.clone(),
                MetavarKind::Natural,
                0,
                None,
            );
            let application = captured.iter().fold(Expr::mvar(abstracted), |head, local| {
                Expr::app(head, Expr::fvar(local.id.clone()))
            });
            self.txn
                .assign_mvar(
                    id.clone(),
                    application,
                    AssignmentJustification::SyntheticHole,
                )
                .map_err(|error| {
                    failure(SourceInferenceError::Unification(Box::new(
                        UnificationError::Metavariable(error),
                    )))
                })?;
            assigned = true;
        }
        Ok(assigned)
    }

    /// Retry every postponed coercion once, in its own local context. True
    /// when one completed, so synthesis has new work to resume.
    pub(in crate::source) fn resume_postponed_coercions(
        &mut self,
    ) -> Result<bool, NatDefinitionElabError> {
        let pending = std::mem::take(&mut self.postponed_coercions);
        let mut waiting = Vec::new();
        let mut progressed = false;
        for record in pending {
            self.tick()?;
            let saved = std::mem::replace(&mut self.txn.lctx, record.lctx.clone());
            let completed = self.complete_coercion(&record.term, &record.expected);
            self.txn.lctx = saved;
            match completed? {
                Some(value) => {
                    self.constrain(&record.hole, &value)?;
                    progressed = true;
                }
                None => waiting.push(record),
            }
        }
        let added = std::mem::replace(&mut self.postponed_coercions, waiting);
        self.postponed_coercions.extend(added);
        Ok(progressed)
    }

    /// Synthesis is over: a coercion still open is the mismatch it was
    /// postponed from, refused or left to K1 as `coerce_expected` would have.
    pub(in crate::source) fn finish_postponed_coercions(
        &mut self,
    ) -> Result<(), NatDefinitionElabError> {
        for record in std::mem::take(&mut self.postponed_coercions) {
            self.tick()?;
            let saved = std::mem::replace(&mut self.txn.lctx, record.lctx.clone());
            let result = (|| {
                self.refute_rigid_mismatch(&record.term.type_, &record.expected)?;
                self.constrain_expected_type(&record.term.type_, &record.expected)?;
                self.constrain(&record.hole, &record.term.value)
            })();
            self.txn.lctx = saved;
            result?;
        }
        Ok(())
    }

    /// One speculative `CoeT` attempt; only a complete path commits.
    fn complete_coercion(
        &mut self,
        term: &Typed,
        expected: &Expr,
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        let mut trial = self.clone();
        let result = (|| {
            let Some(candidate) = trial.coerce_value(term, expected)? else {
                return Ok(None);
            };
            if !trial.coercion_eq(&candidate.type_, expected)? {
                return Ok(None);
            }
            Ok(Some(candidate.value))
        })();
        self.txn.budget.heartbeats_consumed = trial.txn.budget.heartbeats_consumed;
        match result {
            Ok(Some(value)) => {
                *self = trial;
                Ok(Some(value))
            }
            Ok(None) => Ok(None),
            Err(error) if nonmatch(&error) => Ok(None),
            Err(error) => Err(error),
        }
    }
}
