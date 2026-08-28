//! Decision ledger and deterministic audit log for Athanor (plan §10.1, §7).
//!
//! Records every choice, branch, tactic attempt, unification step, or instance resolution
//! made during elaboration for causal proof graph construction and replayability.

use fln_core::expr::{Expr, MVarId};
use fln_core::name::Name;

/// A structured record of an elaboration decision.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DecisionRecord {
    /// Branch taken in an overloaded / polymorphic application.
    OverloadChoice {
        candidate_name: Name,
        index: usize,
        total_candidates: usize,
    },
    /// Tactic executed on a specific goal.
    TacticApplication {
        tactic: Name,
        target_goal: MVarId,
        new_goals: Vec<MVarId>,
    },
    /// Coercion inserted between source and expected types.
    CoercionInsertion {
        from_type: Expr,
        to_type: Expr,
        coercion_decl: Name,
    },
    /// Typeclass instance selected.
    InstanceResolution {
        class_name: Name,
        instance_name: Name,
    },
    /// Speculative fork or child transaction started.
    TransactionFork {
        branch_id: usize,
        num_alternatives: usize,
    },
    /// Child transaction rolled back.
    TransactionRollback { branch_id: usize, reason: String },
}

/// Append-only ledger recording elaboration decisions.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct DecisionLedger {
    records: Vec<DecisionRecord>,
}

impl DecisionLedger {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn is_empty(&self) -> bool {
        self.records.is_empty()
    }

    pub fn len(&self) -> usize {
        self.records.len()
    }

    pub fn records(&self) -> &[DecisionRecord] {
        &self.records
    }

    pub fn record(&mut self, entry: DecisionRecord) {
        self.records.push(entry);
    }

    pub fn append(&mut self, other: &mut DecisionLedger) {
        self.records.append(&mut other.records);
    }

    pub fn truncate(&mut self, checkpoint: usize) {
        self.records.truncate(checkpoint);
    }
}
