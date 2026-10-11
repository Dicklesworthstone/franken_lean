//! Pending instance synthesis inside native unification (plan §10.2).
//!
//! The pin's `isDefEq`, stuck on an instance metavariable, calls
//! `synthPending` (vendored `Lean/Meta/ExprDefEq.lean`, `unstuckMVar`, and
//! `Lean/Meta/SynthInstance.lean`, `synthPendingImp`): once unification has
//! fixed the class inputs, the instance is synthesized and unification goes on
//! with the assignments it already made. This solver owns no instance search:
//! at a fixed point it asks the owner of an opaque source instance hole or an
//! ordinary candidate dictionary that blocks reduction. The answer takes
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
    /// Synthesize the instance hole `goal` against `state`, the batch's working
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
    /// One `synthPending` step at a fixed point: ask for the first owned opaque
    /// hole or ordinary reduction blocker that the owner can solve now, in
    /// deterministic equation order. Returns whether one was assigned.
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
        for (left, right, locals) in postponed {
            for side in [left, right] {
                let side = self.instantiate(side)?;
                self.opaque_holes(&side, &mut seen, &mut goals)?;
                if let Some(goal) = self.assignable_blocker(&side, locals)?
                    && seen.insert(goal.clone())
                {
                    goals.push(goal);
                }
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

    /// Follow the reduction blocker, not every ordinary hole in an expression.
    /// The pin's `getStuckMVar?` follows flexible heads and class projection
    /// receivers. Candidate dictionaries are ordinary metavariables, so the
    /// opaque-hole scan alone cannot resume their stuck parent projections.
    /// The owner still decides whether a discovered hole is an instance goal.
    fn assignable_blocker(
        &mut self,
        expr: &Expr,
        locals: &LocalContext,
    ) -> Result<Option<MVarId>, UnificationError> {
        let mut current = expr.clone();
        loop {
            self.meter.node()?;
            if !current.has_expr_mvar() {
                return Ok(None);
            }
            current = self.whnf(&current, locals)?;
            let mut head = current.clone();
            let mut arguments = Vec::new();
            while let ExprNode::App { f, a } = head.node() {
                self.meter.node()?;
                arguments.push(a.clone());
                head = f.clone();
            }
            match head.node() {
                ExprNode::MVar { id } => {
                    let assignable = self.work.mvars.get_decl(id).is_some_and(|declaration| {
                        declaration.kind != MetavarKind::SyntheticOpaque
                            && declaration.delayed.is_none()
                            && !self.work.mvars.is_assigned(id)
                    });
                    return Ok(assignable.then(|| id.clone()));
                }
                ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => {
                    current = expr.clone();
                }
                ExprNode::Const { name, levels } => {
                    let Some(ConstantInfo::Defn(definition)) = self.work.env.find(name) else {
                        return Ok(None);
                    };
                    if definition.base.level_params.len() != levels.len() {
                        return Ok(None);
                    }
                    let Some(projection) = crate::records::projection::class_projection(
                        &self.work.env,
                        definition,
                        || self.meter.node(),
                    )?
                    else {
                        return Ok(None);
                    };
                    if arguments.len() <= projection.parameters
                        || !self
                            .projection_registry
                            .read(&self.work.env)
                            .map_err(UnificationError::InstanceRegistry)?
                            .is_class(&projection.structure)
                    {
                        return Ok(None);
                    }
                    current = arguments[arguments.len() - projection.parameters - 1].clone();
                }
                _ => return Ok(None),
            }
        }
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
