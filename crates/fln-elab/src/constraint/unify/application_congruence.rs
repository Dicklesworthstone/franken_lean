//! The metavariable case of the pin's `tryHeuristic`/`unfoldBothDefEq`
//! (`Lean/Meta/ExprDefEq.lean`). Try the arguments of two applications of the
//! same definition before unfolding that definition. This is a reversible
//! guess, never an injectivity rule: a failed guess resumes ordinary delta.
use super::*;
use fln_core::expr::BinderInfo;

// Nested argument comparisons can expose further definition applications.
// At this depth the optional heuristic yields to the ordinary worklist rather
// than growing the Rust stack with the expression's unbounded nesting depth.
pub(super) const MAX_CONGRUENCE_DEPTH: u8 = 16;

pub(super) enum CongruenceResult {
    Solved,
    Refused { made_assignments: bool },
}

impl Engine<'_> {
    pub(super) fn try_definition_congruence(
        &mut self,
        left: &Expr,
        right: &Expr,
        locals: &LocalContext,
    ) -> Result<bool, UnificationError> {
        if self.budget.transparency != UnificationTransparency::Default {
            return Ok(false);
        }
        self.try_shared_head_congruence(left, right, locals)
    }

    /// The pin's same-head heuristic without its transparency gate: compare
    /// the arguments, then the universe levels, of two applications of one
    /// unfoldable definition, in a trial that commits only a complete solution.
    pub(super) fn try_shared_head_congruence(
        &mut self,
        left: &Expr,
        right: &Expr,
        locals: &LocalContext,
    ) -> Result<bool, UnificationError> {
        if self.congruence_depth >= MAX_CONGRUENCE_DEPTH
            || (!left.has_expr_mvar() && !right.has_expr_mvar())
        {
            return Ok(false);
        }
        let (left_head, left_arguments) = self.congruence_spine(left)?;
        let (right_head, right_arguments) = self.congruence_spine(right)?;
        if left_arguments.is_empty() || left_arguments.len() != right_arguments.len() {
            return Ok(false);
        }
        let (
            ExprNode::Const { name, levels },
            ExprNode::Const {
                name: right_name,
                levels: right_levels,
            },
        ) = (left_head.node(), right_head.node())
        else {
            return Ok(false);
        };
        if name != right_name || levels.len() != right_levels.len() {
            return Ok(false);
        }
        let Some(ConstantInfo::Defn(definition)) = self.work.env.find(name) else {
            return Ok(false);
        };
        if definition.safety != DefinitionSafety::Safe
            || definition.base.level_params.len() != levels.len()
            || crate::reducibility::table(&self.work.env)
                .map_err(UnificationError::Reducibility)?
                .status(name)
                == crate::reducibility::Reducibility::Irreducible
        {
            return Ok(false);
        }

        // Arguments precede universe levels, as at the pin. An early rigid
        // argument can fix the type of a later argument or universe equation.
        let mut equations = Vec::with_capacity(left_arguments.len() + levels.len());
        for (left, right) in left_arguments.into_iter().zip(right_arguments) {
            self.meter.node()?;
            equations.push((left, right, locals.clone()));
        }
        for (left, right) in levels.iter().zip(right_levels) {
            self.meter.node()?;
            equations.push((
                Expr::sort(left.clone()),
                Expr::sort(right.clone()),
                locals.clone(),
            ));
        }
        // At `instances` transparency this rung precedes the unfolding path it falls back
        // to; a refused trial must cost what the pin's failing `isDefEqArgs` costs.
        let fail_fast = self.budget.transparency == UnificationTransparency::Instances;
        Ok(matches!(
            self.try_congruence_equations(&equations, fail_fast, true)?,
            CongruenceResult::Solved
        ))
    }

    /// At `Abbreviations` (`.reducible`) transparency, `isDefEqArgs` checks
    /// instance-implicit (`[..]`) arguments of same-head applications with
    /// `withImplicitConfig` (`withAtLeastTransparency .instances`, vendored
    /// `Lean/Meta/ExprDefEq.lean:351-396`) so instance diamonds resolve during
    /// `rw` and `simp` without unfolding `[implicit_reducible]` functions in
    /// explicit arguments.
    pub(super) fn try_instance_arg_congruence(
        &mut self,
        left: &Expr,
        right: &Expr,
        locals: &LocalContext,
    ) -> Result<Option<CongruenceResult>, UnificationError> {
        if self.budget.transparency != UnificationTransparency::Abbreviations
            || self.congruence_depth >= MAX_CONGRUENCE_DEPTH
        {
            return Ok(None);
        }
        let (left_head, left_arguments) = self.congruence_spine(left)?;
        let (right_head, right_arguments) = self.congruence_spine(right)?;
        if left_arguments.is_empty() || left_arguments.len() != right_arguments.len() {
            return Ok(None);
        }
        let (
            ExprNode::Const { name, levels },
            ExprNode::Const {
                name: right_name,
                levels: right_levels,
            },
        ) = (left_head.node(), right_head.node())
        else {
            return Ok(None);
        };
        if name != right_name || levels.len() != right_levels.len() {
            return Ok(None);
        }
        let Some(constant) = self.work.env.find(name) else {
            return Ok(None);
        };
        let mut binder_infos = Vec::with_capacity(left_arguments.len());
        let mut cursor = &constant.constant_val().type_;
        while binder_infos.len() < left_arguments.len() {
            self.meter.node()?;
            match cursor.node() {
                ExprNode::MData { expr, .. } => cursor = expr,
                ExprNode::ForallE {
                    binder_info, body, ..
                } => {
                    binder_infos.push(*binder_info);
                    cursor = body;
                }
                _ => break,
            }
        }
        if !binder_infos.contains(&BinderInfo::InstImplicit) {
            return Ok(None);
        }

        let mut first_pass = Vec::with_capacity(left_arguments.len() + levels.len());
        let mut inst_pass = Vec::new();
        for (index, (lhs, rhs)) in left_arguments.into_iter().zip(right_arguments).enumerate() {
            self.meter.node()?;
            if self.same_up_to_assignment(&lhs, &rhs)? {
                continue;
            }
            let is_inst = binder_infos.get(index) == Some(&BinderInfo::InstImplicit);
            let bare_assignable = |expr: &Expr| -> bool {
                matches!(
                    expr.node(),
                    ExprNode::MVar { id }
                        if !self.work.mvars.is_assigned(id)
                            && self.work.mvars.get_decl(id).is_some_and(|decl| {
                                decl.kind != MetavarKind::SyntheticOpaque
                                    && decl.depth <= self.budget.max_metavar_depth
                            })
                )
            };
            if is_inst && !bare_assignable(&lhs) && !bare_assignable(&rhs) {
                inst_pass.push((lhs, rhs, locals.clone()));
            } else {
                first_pass.push((lhs, rhs, locals.clone()));
            }
        }
        if inst_pass.is_empty() {
            return Ok(None);
        }
        for (lhs, rhs) in levels.iter().zip(right_levels) {
            self.meter.node()?;
            first_pass.push((
                Expr::sort(lhs.clone()),
                Expr::sort(rhs.clone()),
                locals.clone(),
            ));
        }

        let generation = self.generation();
        if !first_pass.is_empty() {
            match self.try_congruence_equations(&first_pass, self.fail_fast, true)? {
                CongruenceResult::Solved => {}
                refused @ CongruenceResult::Refused { .. } => return Ok(Some(refused)),
            }
        }
        // `first_pass` already committed K1-checked assignments (e.g. carrier types
        // and explicit arguments) into `self`, so `inst_pass` now sees them while
        // checking `[..]` arguments at `Instances` transparency. If `inst_pass`
        // defers (e.g. waiting on a sibling outer equation), `self` keeps those
        // checked assignments and postpones the outer application for replay.
        let saved_transparency = self.budget.transparency;
        self.budget.transparency = UnificationTransparency::Instances;
        let inst_result = self.try_congruence_equations(&inst_pass, self.fail_fast, true);
        self.budget.transparency = saved_transparency;
        let outcome = match inst_result? {
            CongruenceResult::Solved => CongruenceResult::Solved,
            CongruenceResult::Refused { made_assignments } => CongruenceResult::Refused {
                made_assignments: made_assignments || self.generation() != generation,
            },
        };
        Ok(Some(outcome))
    }

    fn congruence_spine(&mut self, expr: &Expr) -> Result<(Expr, Vec<Expr>), UnificationError> {
        let mut head = expr;
        let mut arguments = Vec::new();
        while let ExprNode::App { f, a } = head.node() {
            self.meter.node()?;
            arguments.push(a.clone());
            head = f;
        }
        arguments.reverse();
        Ok((head.clone(), arguments))
    }

    pub(super) fn try_congruence_equations(
        &mut self,
        equations: &[Equation],
        fail_fast: bool,
        allow_pending: bool,
    ) -> Result<CongruenceResult, UnificationError> {
        // In-place speculative trial with O(delta) undo trails: only mutations
        // actually performed inside this trial are rolled back and metered,
        // avoiding O(mvars.len() + universes.len()) cloning per congruence call.
        self.meter.node()?;
        let saved_constraints = if self.work.constraints.is_empty() {
            None
        } else {
            for _ in 0..self.work.constraints.len() {
                self.meter.node()?;
            }
            Some(self.work.constraints.clone())
        };
        let generation = self.generation();
        let mvar_mark = self.work.mvars.begin_trial();
        let uvar_mark = self.work.universes.begin_trial();
        let reserved_mark = self.reserved_trail.len();
        let checked_mark = self.checked_trail.len();
        let saved_assigned = self.assigned.len();
        let saved_assigned_levels = self.assigned_levels.len();
        let saved_residuals = self.residuals.len();
        let saved_awakened = self.awakened.len();
        let saved_next_local = self.next_local;
        let saved_nat_literals_valid = self.nat_literals_valid;
        let saved_nat_sub_model_valid = self.nat_sub_model_valid;
        let saved_fail_fast = self.fail_fast;
        // Same-head definition congruence mirrors the pin's `checkpointDefEq`
        // around `isDefEqArgs` (`Lean/Meta/ExprDefEq.lean:1510-1512`), where
        // `synthPending` can discharge an instance hole whose carrier an earlier
        // argument just fixed (e.g. `Nat.succ 3 =?= @OfNat.ofNat ?α 4 ?inst`
        // after `?α := Nat`). Record-eta and first-order trials pass
        // `allow_pending = false` so failed probes do not pre-ask the owner.
        let subtrial_pending = if allow_pending {
            self.pending.take_for_subtrial()
        } else {
            pending::PendingState::new(None, u64::MAX)
        };
        let saved_pending = std::mem::replace(&mut self.pending, subtrial_pending);
        self.congruence_depth += 1;
        self.fail_fast = saved_fail_fast || fail_fast;

        let result = self.solve(equations, &[], &[]);

        self.congruence_depth -= 1;
        self.fail_fast = saved_fail_fast;
        let mut used_pending = std::mem::replace(&mut self.pending, saved_pending);
        self.pending.restore_from_subtrial(&mut used_pending);
        let made_assignments = self.generation() != generation;

        match result {
            Ok(()) => {
                self.work.mvars.commit_trial(mvar_mark);
                self.work.universes.commit_trial(uvar_mark);
                if self.congruence_depth == 0 {
                    self.reserved_trail.clear();
                    self.checked_trail.clear();
                }
                Ok(CongruenceResult::Solved)
            }
            Err(error) => {
                let mut undone = self.work.mvars.rollback_trial(mvar_mark);
                undone += self.work.universes.rollback_trial(uvar_mark);
                while self.reserved_trail.len() > reserved_mark {
                    if let Some(id) = self.reserved_trail.pop() {
                        self.reserved.remove(&id);
                        undone += 1;
                    }
                }
                while self.checked_trail.len() > checked_mark {
                    if let Some(id) = self.checked_trail.pop() {
                        self.checked_assignments.remove(&id);
                        undone += 1;
                    }
                }
                self.assigned.truncate(saved_assigned);
                self.assigned_levels.truncate(saved_assigned_levels);
                self.residuals.truncate(saved_residuals);
                self.awakened.truncate(saved_awakened);
                self.next_local = saved_next_local;
                self.nat_literals_valid = saved_nat_literals_valid;
                self.nat_sub_model_valid = saved_nat_sub_model_valid;
                if let Some(constraints) = saved_constraints {
                    self.work.constraints = constraints;
                }
                let recoverable = matches!(
                    &error,
                    UnificationError::Deferred(_)
                        | UnificationError::Metavariable(MetavarError::OccursCheckFailed { .. })
                ) || matches!(
                    &error,
                    UnificationError::AssignmentCheck { outcome, .. }
                        if matches!(&**outcome, Outcome::Complete(Verdict::Rejected { .. }))
                );
                if recoverable {
                    for _ in 0..undone {
                        self.meter.node()?;
                    }
                    Ok(CongruenceResult::Refused { made_assignments })
                } else {
                    Err(error)
                }
            }
        }
    }

    /// Run a read-only (`max_assignments = 0`, `Instances` transparency)
    /// definitional-equality check in-place without cloning `self.work.mvars`
    /// or `self.work.universes`, rolling back any scratch state afterwards.
    pub(super) fn try_frozen_instance_query(
        &mut self,
        left: Expr,
        right: Expr,
        locals: LocalContext,
    ) -> Result<bool, UnificationError> {
        self.meter.node()?;
        let saved_budget = self.budget;
        let mut query_budget = self.budget;
        query_budget.transparency = UnificationTransparency::Instances;
        query_budget.max_assignments = 0;

        let saved_constraints = if self.work.constraints.is_empty() {
            None
        } else {
            for _ in 0..self.work.constraints.len() {
                self.meter.node()?;
            }
            Some(self.work.constraints.clone())
        };
        let mvar_mark = self.work.mvars.begin_trial();
        let uvar_mark = self.work.universes.begin_trial();
        let reserved_mark = self.reserved_trail.len();
        let saved_next_local = self.next_local;
        let saved_assigned = std::mem::take(&mut self.assigned);
        let saved_assigned_levels = std::mem::take(&mut self.assigned_levels);
        let saved_residuals = std::mem::take(&mut self.residuals);
        let saved_awakened = std::mem::take(&mut self.awakened);
        let saved_checked = std::mem::take(&mut self.checked_assignments);
        let saved_checked_trail = std::mem::take(&mut self.checked_trail);
        let saved_fail_fast = self.fail_fast;
        let saved_first_order = self.first_order_trial;
        let saved_pending = std::mem::replace(
            &mut self.pending,
            pending::PendingState::new(None, u64::MAX),
        );

        self.budget = query_budget;
        self.fail_fast = false;
        self.first_order_trial = false;
        self.congruence_depth += 1;

        let result = self.solve(&[(left, right, locals)], &[], &[]);

        self.congruence_depth -= 1;
        self.budget = saved_budget;
        self.fail_fast = saved_fail_fast;
        self.first_order_trial = saved_first_order;
        self.pending = saved_pending;
        let mut undone = self.work.mvars.rollback_trial(mvar_mark);
        undone += self.work.universes.rollback_trial(uvar_mark);
        while self.reserved_trail.len() > reserved_mark {
            if let Some(id) = self.reserved_trail.pop() {
                self.reserved.remove(&id);
                undone += 1;
            }
        }
        self.next_local = saved_next_local;
        self.assigned = saved_assigned;
        self.assigned_levels = saved_assigned_levels;
        self.residuals = saved_residuals;
        self.awakened = saved_awakened;
        self.checked_assignments = saved_checked;
        self.checked_trail = saved_checked_trail;
        if let Some(constraints) = saved_constraints {
            self.work.constraints = constraints;
        }

        match result {
            Ok(()) => {
                for _ in 0..undone {
                    self.meter.node()?;
                }
                Ok(true)
            }
            Err(UnificationError::Deferred(_))
            // This zero is the query's deliberate freeze, not exhaustion of
            // the caller's assignment allowance.
            | Err(UnificationError::AssignmentLimit { limit: 0 })
            | Err(UnificationError::Metavariable(MetavarError::OccursCheckFailed { .. })) => {
                for _ in 0..undone {
                    self.meter.node()?;
                }
                Ok(false)
            }
            Err(error) => Err(error),
        }
    }
}
