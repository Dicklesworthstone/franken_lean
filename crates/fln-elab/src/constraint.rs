//! Constraint queue and postponed obligations for Athanor (plan §10.1, §10.2).
//!
//! Models defeq constraints, typing obligations, typeclass synthesis goals,
//! and delayed assignments with targeted wake-up on metavariable assignment.

use std::collections::{HashMap, HashSet};
use fln_core::expr::{Expr, FVarId, MVarId};

/// Unique identifier for a postponed constraint.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ConstraintId(pub u64);

/// The kind of postponed constraint / obligation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConstraintKind {
    /// Postponed definitional equality between two terms.
    DefEq { lhs: Expr, rhs: Expr },
    /// Expected type check obligation.
    HasType { expr: Expr, expected_type: Expr },
    /// Synthetic typeclass instance synthesis goal.
    SynthInstance { class: Expr, mvar: MVarId },
    /// Higher-order delayed assignment resolution.
    DelayedAssign { mvar: MVarId, fvars: Vec<FVarId>, val: Expr },
}

/// A postponed constraint with its dependency signature and depth.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Constraint {
    pub id: ConstraintId,
    pub kind: ConstraintKind,
    pub reads_mvars: HashSet<MVarId>,
    pub depth: u32,
}

/// Queue of active and suspended constraints with targeted wake-up.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ConstraintQueue {
    next_id: u64,
    constraints: HashMap<ConstraintId, Constraint>,
    /// Index from MVarId to the ConstraintIds that read it.
    mvar_to_constraints: HashMap<MVarId, HashSet<ConstraintId>>,
}

impl ConstraintQueue {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn is_empty(&self) -> bool {
        self.constraints.is_empty()
    }

    pub fn len(&self) -> usize {
        self.constraints.len()
    }

    pub fn constraints(&self) -> &HashMap<ConstraintId, Constraint> {
        &self.constraints
    }

    /// Enqueue a new constraint, automatically indexing the metavariables it reads.
    pub fn enqueue(&mut self, kind: ConstraintKind, reads_mvars: HashSet<MVarId>, depth: u32) -> ConstraintId {
        let id = ConstraintId(self.next_id);
        self.next_id += 1;

        for mvar in &reads_mvars {
            self.mvar_to_constraints.entry(mvar.clone()).or_default().insert(id);
        }

        self.constraints.insert(id, Constraint {
            id,
            kind,
            reads_mvars,
            depth,
        });

        id
    }

    /// Wake up / extract all constraints that read `mvar`.
    ///
    /// Returns the exact woke-up constraints and removes them from the waiting index.
    pub fn wake_up_for_mvar(&mut self, mvar: &MVarId) -> Vec<Constraint> {
        let Some(constraint_ids) = self.mvar_to_constraints.remove(mvar) else {
            return Vec::new();
        };

        let mut woke_up = Vec::new();
        for id in constraint_ids {
            if let Some(constraint) = self.constraints.remove(&id) {
                // Remove from other mvar indices
                for other_mvar in &constraint.reads_mvars {
                    if other_mvar != mvar {
                        if let Some(set) = self.mvar_to_constraints.get_mut(other_mvar) {
                            set.remove(&id);
                        }
                    }
                }
                woke_up.push(constraint);
            }
        }
        woke_up
    }

    /// Remove a specific constraint.
    pub fn remove(&mut self, id: &ConstraintId) -> Option<Constraint> {
        if let Some(constraint) = self.constraints.remove(id) {
            for mvar in &constraint.reads_mvars {
                if let Some(set) = self.mvar_to_constraints.get_mut(mvar) {
                    set.remove(id);
                }
            }
            Some(constraint)
        } else {
            None
        }
    }
}
