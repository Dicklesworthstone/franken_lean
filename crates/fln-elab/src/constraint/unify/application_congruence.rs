//! The metavariable case of the pin's `tryHeuristic`/`unfoldBothDefEq`
//! (`Lean/Meta/ExprDefEq.lean`). Try the arguments of two applications of the
//! same definition before unfolding that definition. This is a reversible
//! guess, never an injectivity rule: a failed guess resumes ordinary delta.
use super::*;

// Nested argument comparisons can expose further definition applications.
// At this depth the optional heuristic yields to the ordinary worklist rather
// than growing the Rust stack with the expression's unbounded nesting depth.
const MAX_CONGRUENCE_DEPTH: u8 = 16;

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
            self.try_congruence_equations(&equations, fail_fast)?,
            CongruenceResult::Solved
        ))
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
    ) -> Result<CongruenceResult, UnificationError> {
        // Account for copying the mutable stores and per-batch identities.
        // Immutable environment/registry data are shared; syntax facts start
        // empty so a large cache is not repeatedly copied by nested trials.
        for _ in 0..self.work.mvars.len()
            + self.work.universes.len()
            + self.reserved.len()
            + self.assigned.len()
            + self.assigned_levels.len()
            + self.residuals.len()
            + self.awakened.len()
        {
            self.meter.node()?;
        }
        let mut trial = Engine {
            work: self.work.clone(),
            budget: self.budget,
            meter: Meter {
                steps: self.meter.steps,
                nodes: self.meter.nodes,
                max_steps: self.meter.max_steps,
                max_nodes: self.meter.max_nodes,
                heartbeat_bound: self.meter.heartbeat_bound,
                cancelled: self.meter.cancelled,
            },
            reserved: self.reserved.clone(),
            next_local: self.next_local,
            assigned: self.assigned.clone(),
            assigned_levels: self.assigned_levels.clone(),
            residuals: self.residuals.clone(),
            awakened: self.awakened.clone(),
            kernel_checks: self.kernel_checks,
            fact_cache: HashMap::new(),
            local_facts: local_facts::Cache::default(),
            nat_literals_valid: self.nat_literals_valid,
            projection_registry: self.projection_registry.clone(),
            // A speculative argument guess cannot invoke an external owner:
            // its side effects are not part of this transaction's checkpoint.
            // If synthesis is needed, delta/fixed-point solving retains the
            // outer owner and can ask it against the surviving equations.
            pending: pending::PendingState::new(None, u64::MAX),
            congruence_depth: self.congruence_depth + 1,
            fail_fast: self.fail_fast || fail_fast,
        };
        let generation = self.generation();
        let result = trial.solve(equations, &[], &[]);
        let made_assignments = trial.generation() != generation;
        // Failed speculation consumes real work. Never reset cancellation,
        // unifier/node limits or the assignment check's typed non-answer.
        self.meter = trial.meter;
        self.kernel_checks = trial.kernel_checks;
        match result {
            Ok(()) => {
                self.work = trial.work;
                self.reserved = trial.reserved;
                self.next_local = trial.next_local;
                self.assigned = trial.assigned;
                self.assigned_levels = trial.assigned_levels;
                self.residuals = trial.residuals;
                self.awakened = trial.awakened;
                self.fact_cache = trial.fact_cache;
                self.local_facts = trial.local_facts;
                self.nat_literals_valid = trial.nat_literals_valid;
                self.projection_registry = trial.projection_registry;
                Ok(CongruenceResult::Solved)
            }
            Err(UnificationError::Deferred(_))
            | Err(UnificationError::Metavariable(MetavarError::OccursCheckFailed { .. })) => {
                Ok(CongruenceResult::Refused { made_assignments })
            }
            Err(UnificationError::AssignmentCheck { outcome, .. })
                if matches!(*outcome, Outcome::Complete(Verdict::Rejected { .. })) =>
            {
                Ok(CongruenceResult::Refused { made_assignments })
            }
            Err(error) => Err(error),
        }
    }
}
