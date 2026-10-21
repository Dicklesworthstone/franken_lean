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
    /// Keep a reduction-blocked application available to `synthPending` before
    /// rigid congruence can discard its projection receiver. Ordinary patterns
    /// have already had their chance. Matching heads retain argument congruence,
    /// which can determine the dictionary without any search. Restrict this to
    /// distinct rigid names with an exactly saturated class projection:
    /// projective heads can solve by singleton inversion or receiver congruence,
    /// and extra field arguments may determine the instance's inputs. Keep
    /// those congruence opportunities. Ordinary reduction and lazy delta have
    /// already had priority at the call.
    pub(super) fn preserve_pending_application(
        &mut self,
        left: &Expr,
        right: &Expr,
        locals: &LocalContext,
    ) -> Result<bool, UnificationError> {
        if self.pending.owner.is_none() || (!left.has_expr_mvar() && !right.has_expr_mvar()) {
            return Ok(false);
        }
        let mut left_head = left;
        let mut left_arity = 0usize;
        while let ExprNode::App { f, .. } = left_head.node() {
            self.meter.node()?;
            left_arity = left_arity
                .checked_add(1)
                .ok_or(UnificationError::ExpressionScope)?;
            left_head = f;
        }
        let mut right_head = right;
        let mut right_arity = 0usize;
        while let ExprNode::App { f, .. } = right_head.node() {
            self.meter.node()?;
            right_arity = right_arity
                .checked_add(1)
                .ok_or(UnificationError::ExpressionScope)?;
            right_head = f;
        }
        match (left_head.node(), right_head.node()) {
            (ExprNode::Const { name: left, .. }, ExprNode::Const { name: right, .. })
                if left != right => {}
            (ExprNode::Const { .. }, ExprNode::FVar { .. })
            | (ExprNode::FVar { .. }, ExprNode::Const { .. }) => {}
            _ => return Ok(false),
        }
        Ok(
            self.saturated_projection_blocker(left, left_head, left_arity, locals)?
                || self.saturated_projection_blocker(right, right_head, right_arity, locals)?,
        )
    }

    /// Stop at the actual receiver boundary, using the admitted projection
    /// body and constructor metadata. An overapplied field still needs ordinary
    /// argument congruence before synthesis, which can fix class inputs.
    fn saturated_projection_blocker(
        &mut self,
        expr: &Expr,
        head: &Expr,
        arity: usize,
        locals: &LocalContext,
    ) -> Result<bool, UnificationError> {
        let ExprNode::Const { name, levels } = head.node() else {
            return Ok(false);
        };
        let Some(ConstantInfo::Defn(definition)) = self.work.env.find(name) else {
            return Ok(false);
        };
        if definition.base.level_params.len() != levels.len() {
            return Ok(false);
        }
        let Some(projection) =
            crate::records::projection::class_projection(&self.work.env, definition, || {
                self.meter.node()
            })?
        else {
            return Ok(false);
        };
        if projection.parameters.checked_add(1) != Some(arity)
            || !self
                .projection_registry
                .read(&self.work.env)
                .map_err(UnificationError::InstanceRegistry)?
                .is_class(&projection.structure)
        {
            return Ok(false);
        }
        let ExprNode::App { a: receiver, .. } = expr.node() else {
            return Ok(false);
        };
        Ok(self.reduction_blocker(receiver, locals)?.is_some())
    }

    /// Try the validated record-eta equations before deciding to retain their
    /// parent. Without an assignment, failed eta can lose the original blocked
    /// projection through later function/application congruence. Keep that
    /// equation for global fixed-point synthesis instead. Ordinary outer
    /// equations still get to determine an exact dictionary before search.
    ///
    /// A trial that made useful assignments must keep the ordinary eta path,
    /// even if a different child refused. Replaying those children preserves
    /// input inference; merely deferring their parent would hide that progress.
    pub(super) fn preserve_pending_record_eta(
        &mut self,
        constructor: &Expr,
        neutral: &Expr,
        locals: &LocalContext,
        children: &[Equation],
    ) -> Result<bool, UnificationError> {
        if self.pending.owner.is_none() || !neutral.has_expr_mvar() {
            return Ok(false);
        }
        // Eta can expose a second ordinary instance hole inside a constructor
        // field. Retaining that constructor would hide the hole from pending
        // reduction-blocker discovery. Keep ordinary eta in that case.
        if constructor.has_expr_mvar() && self.instantiate(constructor)?.has_expr_mvar() {
            return Ok(false);
        }
        let Some(blocker) = self.reduction_blocker(neutral, locals)? else {
            return Ok(false);
        };
        match self.try_congruence_equations(children, false)? {
            super::application_congruence::CongruenceResult::Solved => Ok(true),
            super::application_congruence::CongruenceResult::Refused {
                made_assignments: true,
            } => Ok(false),
            super::application_congruence::CongruenceResult::Refused {
                made_assignments: false,
            } => {
                // Eta can also reveal another instance prerequisite through a
                // record parameter, receiver type, or local let. Only retain
                // the parent when its exposed receiver is the sole remaining
                // expression hole in those equations and dependencies.
                if !self.eta_has_only_receiver_hole(children, &blocker)? {
                    return Ok(false);
                }
                Err(UnificationError::Deferred(
                    UnificationDeferred::UnsupportedEquation,
                ))
            }
        }
    }

    fn eta_has_only_receiver_hole(
        &mut self,
        equations: &[Equation],
        blocker: &MVarId,
    ) -> Result<bool, UnificationError> {
        let Some(declaration) = self.work.mvars.get_decl(blocker) else {
            return Ok(false);
        };
        for _ in 0..declaration.lctx.len() {
            self.meter.node()?;
        }
        let type_ = declaration.type_.clone();
        let locals = declaration.lctx.clone();
        if !self.has_only_receiver_hole(&[type_], &locals, blocker)? {
            return Ok(false);
        }
        for (left, right, locals) in equations {
            if !self.has_only_receiver_hole(&[left.clone(), right.clone()], locals, blocker)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// A conservative dependency check, not instance discovery. Following
    /// referenced locals prevents a let value or dependent local type from
    /// concealing a second ordinary dictionary. No owner is consulted here.
    fn has_only_receiver_hole(
        &mut self,
        roots: &[Expr],
        locals: &LocalContext,
        blocker: &MVarId,
    ) -> Result<bool, UnificationError> {
        let mut pending = Vec::new();
        for root in roots {
            pending.push(self.instantiate(root)?);
        }
        let mut seen = HashSet::new();
        let mut seen_locals = HashSet::new();
        // Pin every visited root so an instantiated temporary cannot donate an
        // allocation identity to another expression in this bounded DAG walk.
        let mut kept = Vec::new();
        while let Some(current) = pending.pop() {
            if (!current.has_expr_mvar() && !current.has_fvar())
                || !seen.insert(current.allocation_identity())
            {
                continue;
            }
            self.meter.node()?;
            match current.node() {
                ExprNode::MVar { id } if id != blocker => return Ok(false),
                ExprNode::FVar { id } if seen_locals.insert(id.clone()) => {
                    let mut found = None;
                    for local in locals.decls() {
                        self.meter.node()?;
                        if &local.id == id {
                            found = Some((local.type_.clone(), local.value.clone()));
                            break;
                        }
                    }
                    let Some((type_, value)) = found else {
                        return Ok(false);
                    };
                    pending.push(self.instantiate(&type_)?);
                    if let Some(value) = value {
                        pending.push(self.instantiate(&value)?);
                    }
                }
                _ => pending.extend(children(&current).into_iter().flatten().cloned()),
            }
            kept.push(current);
        }
        Ok(true)
    }

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
                if let Some(goal) = self.reduction_blocker(&side, locals)?
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
    /// Opaque blockers are returned too, so their original applications survive
    /// congruence; the earlier opaque scan deduplicates them during synthesis.
    /// The owner still decides whether a discovered hole is an instance goal.
    fn reduction_blocker(
        &mut self,
        expr: &Expr,
        locals: &LocalContext,
    ) -> Result<Option<MVarId>, UnificationError> {
        let mut current = expr.clone();
        loop {
            self.meter.node()?;
            // A retained equation can still name a local let whose value
            // contains its reduction blocker. Honor permitted zeta reduction
            // before relying on that expression's syntactic metavariable flag.
            if !current.has_expr_mvar() && (!self.budget.zeta_delta || !current.has_fvar()) {
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
                        declaration.delayed.is_none() && !self.work.mvars.is_assigned(id)
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
