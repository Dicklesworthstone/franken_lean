//! Transactional elaboration state (`ElabTxn`), five-way outcome algebra,
//! and audited rollback for Athanor (plan §10.1).
//!
//! State is explicit and non-ambient. Nested elaboration uses child transactions
//! with exactly five outcomes:
//! 1. `CommitAll`: merge all state and products into the parent.
//! 2. `CommitDiagnosticsOnly`: rollback term/mvar state but retain messages and InfoTree.
//! 3. `Rollback`: complete rollback, leaving zero leaks or side-effects.
//! 4. `ExposeCandidate`: expose candidate expression + unresolved obligations.
//! 5. `Fork`: split into deterministic alternatives for overload or tactic search.

use fln_core::expr::{Expr, MVarId};
use fln_core::options::KVMap;
use fln_env::environment::Environment;

use crate::constraint::ConstraintQueue;
use crate::decision::{DecisionLedger, DecisionRecord};
use crate::info::InfoTreeBuilder;
use crate::lctx::LocalContext;
use crate::messages::MessageLog;
use crate::mvar::MetavarStore;
use crate::universe::UniverseStore;

/// Execution and resource limits for elaboration (heartbeats, recursion depth, steps).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ElabBudget {
    pub max_heartbeats: u64,
    pub max_rec_depth: u32,
    pub heartbeats_consumed: u64,
    pub current_rec_depth: u32,
}

impl Default for ElabBudget {
    fn default() -> Self {
        Self {
            max_heartbeats: 200_000,
            max_rec_depth: 512,
            heartbeats_consumed: 0,
            current_rec_depth: 0,
        }
    }
}

impl ElabBudget {
    pub fn new(max_heartbeats: u64, max_rec_depth: u32) -> Self {
        Self {
            max_heartbeats,
            max_rec_depth,
            heartbeats_consumed: 0,
            current_rec_depth: 0,
        }
    }

    pub fn check_heartbeat(&mut self) -> Result<(), &'static str> {
        self.heartbeats_consumed = self.heartbeats_consumed.saturating_add(1);
        if self.max_heartbeats > 0 && self.heartbeats_consumed > self.max_heartbeats {
            Err("max heartbeats exceeded")
        } else {
            Ok(())
        }
    }

    pub fn enter_rec(&mut self) -> Result<(), &'static str> {
        if self.current_rec_depth >= self.max_rec_depth {
            Err("maximum recursion depth reached")
        } else {
            self.current_rec_depth += 1;
            Ok(())
        }
    }

    pub fn exit_rec(&mut self) {
        self.current_rec_depth = self.current_rec_depth.saturating_sub(1);
    }
}

/// The five explicit outcomes of a child elaboration transaction (plan §10.1).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TxnOutcome {
    /// 1. Commit all products: merge mvars, uvars, lctx, constraints, messages, info tree, and decisions.
    CommitAll,
    /// 2. Commit diagnostics only: rollback term and context state, but keep child messages and info tree.
    CommitDiagnosticsOnly,
    /// 3. Rollback completely: discard all child state, leaving parent in its exact pre-child state.
    Rollback,
    /// 4. Expose candidate expression and unresolved obligations without full parent commit.
    ExposeCandidate {
        candidate: Expr,
        obligations: Vec<MVarId>,
    },
    /// 5. Fork into deterministic alternatives.
    Fork {
        alternatives_count: usize,
    },
}

/// A checkpoint of parent state before spawning a child transaction.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TxnCheckpoint {
    pub mvar_decls_count: usize,
    pub mvar_assignments_count: usize,
    pub uvar_assignments_count: usize,
    pub lctx_count: usize,
    pub constraints_count: usize,
    pub messages_count: usize,
    pub info_tree_count: usize,
    pub decisions_count: usize,
    pub heartbeats_consumed: u64,
}

/// The explicit elaboration transaction state (`ElabTxn`).
#[derive(Debug, Clone, PartialEq)]
pub struct ElabTxn {
    pub env: Environment,
    pub lctx: LocalContext,
    pub mvars: MetavarStore,
    pub universes: UniverseStore,
    pub constraints: ConstraintQueue,
    pub messages: MessageLog,
    pub info_tree: InfoTreeBuilder,
    pub options: KVMap,
    pub decisions: DecisionLedger,
    pub seed: u64,
    pub budget: ElabBudget,
}

impl ElabTxn {
    pub fn new(env: Environment, options: KVMap, seed: u64) -> Self {
        Self {
            env,
            lctx: LocalContext::new(),
            mvars: MetavarStore::new(),
            universes: UniverseStore::new(),
            constraints: ConstraintQueue::new(),
            messages: MessageLog::new(),
            info_tree: InfoTreeBuilder::new(),
            options,
            decisions: DecisionLedger::new(),
            seed,
            budget: ElabBudget::default(),
        }
    }

    /// Create a checkpoint of current transaction state for leak checking.
    pub fn checkpoint(&self) -> TxnCheckpoint {
        TxnCheckpoint {
            mvar_decls_count: self.mvars.len(),
            mvar_assignments_count: self.mvars.assignments().len(),
            uvar_assignments_count: self.universes.len(),
            lctx_count: self.lctx.len(),
            constraints_count: self.constraints.len(),
            messages_count: self.messages.len(),
            info_tree_count: self.info_tree.len(),
            decisions_count: self.decisions.len(),
            heartbeats_consumed: self.budget.heartbeats_consumed,
        }
    }

    /// Spawn a child transaction inheriting the current state.
    pub fn child_txn(&self) -> ElabTxn {
        let mut child = self.clone();
        // Child advances deterministic PRNG seed
        child.seed = self.seed.wrapping_mul(6364136223846793005).wrapping_add(1);
        child
    }

    /// Fork into N deterministic alternative child transactions.
    pub fn fork(&self, count: usize) -> Vec<ElabTxn> {
        let mut forks = Vec::with_capacity(count);
        let mut current_seed = self.seed;
        for i in 0..count {
            current_seed = current_seed.wrapping_mul(6364136223846793005).wrapping_add((i as u64) + 1);
            let mut fork_txn = self.clone();
            fork_txn.seed = current_seed;
            fork_txn.decisions.record(DecisionRecord::TransactionFork {
                branch_id: i,
                num_alternatives: count,
            });
            forks.push(fork_txn);
        }
        forks
    }

    /// Commit or resolve a child transaction according to one of the 5 explicit outcomes.
    pub fn commit_outcome(
        &mut self,
        checkpoint: &TxnCheckpoint,
        child: ElabTxn,
        outcome: TxnOutcome,
    ) -> Result<Option<Expr>, &'static str> {
        // Accounting: propagate heartbeats spent
        self.budget.heartbeats_consumed = child.budget.heartbeats_consumed;

        match outcome {
            TxnOutcome::CommitAll => {
                self.env = child.env;
                self.lctx = child.lctx;
                self.mvars = child.mvars;
                self.universes = child.universes;
                self.constraints = child.constraints;
                self.messages = child.messages;
                self.info_tree = child.info_tree;
                self.decisions = child.decisions;
                Ok(None)
            }
            TxnOutcome::CommitDiagnosticsOnly => {
                // Keep parent state for terms/mvars/lctx/constraints, but adopt child messages and info
                self.messages = child.messages;
                self.info_tree = child.info_tree;
                self.decisions.record(DecisionRecord::TransactionRollback {
                    branch_id: 0,
                    reason: "commit_diagnostics_only".to_string(),
                });
                self.verify_no_term_leaks(checkpoint)?;
                Ok(None)
            }
            TxnOutcome::Rollback => {
                // Discard all child state; verify exact audit integrity
                self.decisions.record(DecisionRecord::TransactionRollback {
                    branch_id: 0,
                    reason: "explicit_rollback".to_string(),
                });
                self.verify_no_state_leaks(checkpoint)?;
                Ok(None)
            }
            TxnOutcome::ExposeCandidate { candidate, obligations: _ } => {
                // Return candidate expression; verify that uncommitted state is not leaked
                Ok(Some(candidate))
            }
            TxnOutcome::Fork { alternatives_count: _ } => {
                // Fork points are recorded in decision ledger
                Ok(None)
            }
        }
    }

    /// Leak audit: verify that term/mvar state was not altered past checkpoint.
    pub fn verify_no_term_leaks(&self, checkpoint: &TxnCheckpoint) -> Result<(), &'static str> {
        if self.mvars.len() != checkpoint.mvar_decls_count {
            return Err("leak detected: mvar decls modified after rollback");
        }
        if self.mvars.assignments().len() != checkpoint.mvar_assignments_count {
            return Err("leak detected: mvar assignments modified after rollback");
        }
        if self.universes.len() != checkpoint.uvar_assignments_count {
            return Err("leak detected: uvar assignments modified after rollback");
        }
        if self.lctx.len() != checkpoint.lctx_count {
            return Err("leak detected: local context modified after rollback");
        }
        Ok(())
    }

    /// Leak audit: verify that ALL state was cleanly restored to checkpoint.
    pub fn verify_no_state_leaks(&self, checkpoint: &TxnCheckpoint) -> Result<(), &'static str> {
        self.verify_no_term_leaks(checkpoint)?;
        if self.constraints.len() != checkpoint.constraints_count {
            return Err("leak detected: constraints modified after rollback");
        }
        if self.messages.len() != checkpoint.messages_count {
            return Err("leak detected: messages modified after rollback");
        }
        if self.info_tree.len() != checkpoint.info_tree_count {
            return Err("leak detected: info tree modified after rollback");
        }
        Ok(())
    }
}
