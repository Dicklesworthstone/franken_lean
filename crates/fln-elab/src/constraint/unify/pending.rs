//! Pending instance synthesis inside native unification (plan §10.2).
//!
//! The pin's `isDefEq`, stuck on an instance metavariable, calls
//! `synthPending` (vendored `Lean/Meta/ExprDefEq.lean`, `unstuckMVar`, and
//! `Lean/Meta/SynthInstance.lean`, `synthPendingImp`): once unification has
//! fixed the class inputs, the instance is synthesized and unification goes on
//! with the assignments it already made. This solver keeps instance holes
//! opaque and owns no instance search, so at a fixed point blocked on such a
//! hole it asks the hole's owner instead. The answer is not trusted: it takes
//! the same scope check, worklist typing equation and final K1 validation as a
//! pattern solution, and the batch stays all-or-nothing. A declined goal is
//! asked again only after a new assignment could have changed its inputs.
use super::*;
use crate::mvar::MetavarDecl;

/// The owner's answer to one [`PendingSynthesis::synthesize`] request.
pub struct PendingAnswer {
    /// `Ok(Some((value, class)))` is a complete instance of class `class` for
    /// the goal, closed over the goal's local context. `Ok(None)` declines: the
    /// goal is not the owner's, or its inputs are still unknown. An error is a
    /// non-answer, such as exhaustion, and ends the batch with that error.
    pub result: Result<Option<(Expr, Name)>, UnificationError>,
    /// Heartbeats the request consumed. They are charged even on error.
    pub spent: u64,
}

/// The owner of instance holes, consulted as the pin consults `synthPending`.
pub trait PendingSynthesis {
    /// Synthesize the opaque hole `goal` against `state`, the batch's working
    /// transaction; its new assignments are validated only when the batch ends.
    /// `spent` heartbeats of the caller's budget are already used by this batch.
    fn synthesize(&mut self, state: &ElabTxn, goal: &MVarId, spent: u64) -> PendingAnswer;
}

pub(super) struct PendingState<'a> {
    owner: Option<&'a mut dyn PendingSynthesis>,
    /// Transaction heartbeats available when the batch started.
    remaining: u64,
    spent: u64,
    generation: Option<usize>,
    declined: HashSet<MVarId>,
}

impl<'a> PendingState<'a> {
    pub(super) fn new(owner: Option<&'a mut dyn PendingSynthesis>, remaining: u64) -> Self {
        Self {
            owner,
            remaining,
            spent: 0,
            generation: None,
            declined: HashSet::new(),
        }
    }

    pub(super) fn spent(&self) -> u64 {
        self.spent
    }
}

impl Engine<'_> {
    /// One `synthPending` step at a fixed point: ask for the first unassigned
    /// opaque hole, in deterministic order of occurrence in the postponed
    /// equations, that the owner can solve now. Returns whether one was assigned.
    pub(super) fn synthesize_pending(
        &mut self,
        postponed: &VecDeque<Equation>,
        pending: &mut VecDeque<Equation>,
    ) -> Result<bool, UnificationError> {
        if self.pending.owner.is_none() {
            return Ok(false);
        }
        let generation = self.generation();
        if self.pending.generation != Some(generation) {
            self.pending.generation = Some(generation);
            self.pending.declined.clear();
        }
        let mut goals = Vec::new();
        let mut seen = HashSet::new();
        for (left, right, _) in postponed {
            for side in [left, right] {
                let side = self.instantiate(side)?;
                self.opaque_holes(&side, &mut seen, &mut goals)?;
            }
        }
        for goal in goals {
            self.meter.tick()?;
            if !self.pending.declined.insert(goal.clone()) {
                continue;
            }
            let Some(declaration) = self.work.mvars.get_decl(&goal).cloned() else {
                continue;
            };
            // A hole of an outer metavariable depth is read-only here.
            if declaration.depth > self.budget.max_metavar_depth {
                continue;
            }
            // The owner's own unification batches must not reuse an identity
            // this batch has already opened.
            self.work.mvars.advance_unify_locals(self.next_local);
            let already = self.meter.steps.saturating_add(self.pending.spent);
            let owner = self
                .pending
                .owner
                .as_deref_mut()
                .expect("an owner was checked above");
            let answer = owner.synthesize(&self.work, &goal, already);
            self.charge_pending(answer.spent)?;
            let Some((value, class_name)) = answer.result? else {
                continue;
            };
            if self.assign_pending(&goal, &declaration, value, class_name, pending)? {
                return Ok(true);
            }
        }
        Ok(false)
    }

    /// Unassigned opaque holes of `expr`, first occurrence first.
    fn opaque_holes(
        &mut self,
        expr: &Expr,
        seen: &mut HashSet<MVarId>,
        goals: &mut Vec<MVarId>,
    ) -> Result<(), UnificationError> {
        let mut visited = HashSet::new();
        let mut stack = vec![expr];
        while let Some(current) = stack.pop() {
            if !current.has_expr_mvar() || !visited.insert(std::ptr::from_ref(current.node())) {
                continue;
            }
            self.meter.node()?;
            if let ExprNode::MVar { id } = current.node() {
                let opaque =
                    self.work.mvars.get_decl(id).is_some_and(|declaration| {
                        declaration.kind == MetavarKind::SyntheticOpaque
                    });
                if opaque && !self.work.mvars.is_assigned(id) && seen.insert(id.clone()) {
                    goals.push(id.clone());
                }
                continue;
            }
            stack.extend(children(current).into_iter().rev().flatten());
        }
        Ok(())
    }

    /// Synthesis work comes out of the same transaction budget as the batch.
    fn charge_pending(&mut self, spent: u64) -> Result<(), UnificationError> {
        self.pending.spent = self
            .pending
            .spent
            .checked_add(spent)
            .ok_or(UnificationError::HeartbeatLimit)?;
        let left = self.pending.remaining.saturating_sub(self.pending.spent);
        if left <= self.meter.max_steps {
            self.meter.max_steps = left;
            self.meter.heartbeat_bound = true;
        }
        if self.meter.steps >= self.meter.max_steps {
            return Err(UnificationError::HeartbeatLimit);
        }
        Ok(())
    }

    /// Assign an owner's answer exactly as a solved pattern: no free local
    /// outside the hole's context, a worklist equation for its type, the
    /// assignment budget, and final K1 validation with the batch. An answer
    /// this solver cannot place is declined, never published unchecked.
    fn assign_pending(
        &mut self,
        goal: &MVarId,
        declaration: &MetavarDecl,
        value: Expr,
        class_name: Name,
        pending: &mut VecDeque<Equation>,
    ) -> Result<bool, UnificationError> {
        if value.has_loose_bvars() {
            return Err(UnificationError::LooseBoundVariable);
        }
        let value = self.instantiate(&value)?;
        if value.has_expr_mvar() || value.has_level_mvar() {
            return Ok(false);
        }
        let free = self.scan(&value)?.fvars;
        if free.iter().any(|id| !declaration.lctx.contains(id)) {
            return Ok(false);
        }
        let typing =
            self.assignment_type_equation(&declaration.type_, &value, &declaration.lctx)?;
        self.assignment_slot()?;
        let awakened = self
            .work
            .assign_mvar(
                goal.clone(),
                value,
                AssignmentJustification::InstanceSearch { class_name },
            )
            .map_err(UnificationError::Metavariable)?;
        self.awakened.extend(awakened);
        self.assigned.push(goal.clone());
        if let Some(equation) = typing {
            pending.push_front(equation);
        }
        Ok(true)
    }
}
