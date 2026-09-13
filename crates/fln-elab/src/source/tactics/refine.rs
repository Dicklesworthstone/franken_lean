//! Partial proof terms with explicitly scoped synthetic goals.
//!
//! A hole under a lambda must not be a bare metavariable whose hidden context
//! escapes when that lambda closes. Represent each hole by a closed function
//! metavariable applied to its captured locals, and close that same telescope
//! when its proof-state goal is solved. All transport is explicit core syntax.
use super::*;

#[derive(Clone, Default)]
pub(in crate::source) struct RefinementFrame {
    holes: Vec<(Option<Name>, ProofGoal)>,
}

impl Context {
    pub(in crate::source) fn begin_refinement(&mut self) -> usize {
        let depth = self.refinements.len();
        self.refinements.push(RefinementFrame::default());
        depth
    }

    pub(in crate::source) fn synthetic_proof_hole(
        &mut self,
        name: Option<Name>,
        expected: Option<&Expr>,
    ) -> Result<Typed, NatDefinitionElabError> {
        if self.refinements.is_empty() {
            return Err(error(TacticError::SyntheticHoleOutsideRefine));
        }
        self.tick()?;
        let type_ = match expected {
            Some(type_) => type_.clone(),
            None => {
                let sort = self.type_expected()?;
                self.hole(sort)?
            }
        };
        let existing = name.as_ref().and_then(|name| {
            self.refinements.last().and_then(|frame| {
                frame
                    .holes
                    .iter()
                    .find(|(found, _)| found.as_ref() == Some(name))
                    .map(|(_, goal)| goal.clone())
            })
        });
        let goal = if let Some(goal) = existing {
            // Reuse is intentionally scoped to an identical captured context.
            // Equal spelling in different binder scopes cannot capture a local.
            if goal.lctx != self.txn.lctx || !self.proof_types_match(&goal.target, &type_)? {
                return Err(error(TacticError::IncompatibleSyntheticHole));
            }
            goal
        } else {
            let locals = self.txn.lctx.decls().to_vec();
            let mut closed_type = type_.clone();
            for local in locals.iter().rev() {
                self.tick()?;
                closed_type = closed_type
                    .abstract_fvar(&local.id, 0)
                    .map_err(|_| failure(SourceInferenceError::Scope))?;
                closed_type = if let Some(value) = &local.value {
                    Expr::let_e(
                        local.user_name.clone(),
                        local.type_.clone(),
                        value.clone(),
                        closed_type,
                        false,
                    )
                } else {
                    Expr::forall_e(
                        local.user_name.clone(),
                        local.type_.clone(),
                        closed_type,
                        local.binder_info,
                    )
                };
            }
            let id = MVarId(self.fresh_name()?);
            self.txn.mvars.declare(
                id.clone(),
                name.clone().unwrap_or_else(|| id.0.clone()),
                closed_type,
                LocalContext::new(),
                MetavarKind::SyntheticOpaque,
                0,
                None,
            );
            let goal = ProofGoal {
                id,
                target: type_.clone(),
                lctx: self.txn.lctx.clone(),
                introduced: locals,
            };
            self.refinements
                .last_mut()
                .expect("active refinement")
                .holes
                .push((name, goal.clone()));
            goal
        };
        let mut value = Expr::mvar(goal.id);
        for local in goal.lctx.decls() {
            self.tick()?;
            if local.value.is_none() {
                value = Expr::app(value, Expr::fvar(local.id.clone()));
            }
        }
        Ok(Typed { value, type_ })
    }

    pub(in crate::source) fn finish_refinement(
        &mut self,
        proof: &mut ProofState<'_>,
        goal: ProofGoal,
        term: Typed,
        depth: usize,
    ) -> Result<(), NatDefinitionElabError> {
        if self.refinements.len() != depth + 1 {
            return Err(error(TacticError::MalformedScript));
        }
        let frame = self.refinements.pop().expect("checked refinement depth");
        self.txn.lctx = goal.lctx.clone();
        self.resolve_instances(false)?;
        self.flush(false)?;
        // The parent is closed only after all holes, including holes in unused
        // let values or annotations, have supplied their actual checked terms.
        proof.work.push(Work::Close(goal, term.value));
        proof.work.extend(
            frame
                .holes
                .into_iter()
                .rev()
                .map(|(_, goal)| Work::Goal(goal)),
        );
        Ok(())
    }
}
