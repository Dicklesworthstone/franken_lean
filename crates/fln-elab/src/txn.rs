//! Transactional elaboration state (`ElabTxn`), five-way outcome algebra,
//! and audited rollback for Athanor (plan §10.1).
//!
//! Semantic state is explicit and non-ambient. A failed alternative cannot
//! publish its assignments or erase work already charged to its parent.
//! Candidate exposure preserves the context needed to interpret its holes;
//! an exposed candidate is untrusted elaboration output, not kernel admission.

use fln_core::expr::{Expr, MVarId};
use fln_core::options::KVMap;
use fln_env::environment::Environment;

use crate::constraint::{Constraint, ConstraintId, ConstraintKind, ConstraintQueue};
use crate::decision::{DecisionLedger, DecisionRecord};
use crate::info::InfoTreeBuilder;
use crate::lctx::LocalContext;
use crate::messages::MessageLog;
use crate::mvar::{AssignmentJustification, MetavarError, MetavarStore};
use crate::universe::{UniverseInstantiationError, UniverseStore};

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
        self.heartbeats_consumed = self
            .heartbeats_consumed
            .checked_add(1)
            .ok_or("heartbeat counter overflow")?;
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
    /// Commit all semantic products, including options and deterministic seed.
    CommitAll,
    /// Roll back semantic state, retaining child messages and InfoTree.
    CommitDiagnosticsOnly,
    /// Discard child semantic state. Work accounting and the audit event survive.
    Rollback,
    /// Retain candidate, obligations and their child context without publishing it.
    ExposeCandidate {
        candidate: Expr,
        obligations: Vec<MVarId>,
    },
    /// Record a fork point. `ElabTxn::fork` constructs the alternative states.
    Fork { alternatives_count: usize },
}

/// An untrusted candidate together with the state in which its holes and free
/// variables have meaning. It does not contain a nested candidate history.
#[derive(Debug, Clone, PartialEq)]
pub struct ExposedCandidate {
    pub expression: Expr,
    pub obligations: Vec<MVarId>,
    pub env: Environment,
    pub lctx: LocalContext,
    pub mvars: MetavarStore,
    pub universes: UniverseStore,
    pub constraints: ConstraintQueue,
    pub options: KVMap,
    pub seed: u64,
}

impl ExposedCandidate {
    /// Read the candidate under its retained assignments. Unresolved expression
    /// metavariables remain explicit; this operation is not a proof check.
    pub fn instantiate_expr(&self) -> Result<Expr, UniverseInstantiationError> {
        self.universes
            .instantiate_expr(&self.mvars.instantiate(&self.expression))
    }
}

/// A checkpoint before spawning a child. Counts remain diagnostic summaries;
/// private value snapshots, not caller-editable counts, drive leak detection.
#[derive(Debug, Clone, PartialEq)]
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
    snapshot: Box<ElabTxn>,
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
    /// The most recent exposed candidate, consumed with `take_exposed_candidate`.
    pub exposed_candidate: Option<ExposedCandidate>,
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
            exposed_candidate: None,
        }
    }

    /// Postpone an obligation using its current term/context dependencies.
    pub fn postpone(&mut self, kind: ConstraintKind, depth: u32) -> ConstraintId {
        self.constraints.enqueue_inferred(kind, &self.mvars, depth)
    }

    /// Assign and return the deterministically ordered obligations to retry.
    pub fn assign_mvar(
        &mut self,
        id: MVarId,
        value: Expr,
        justification: AssignmentJustification,
    ) -> Result<Vec<Constraint>, MetavarError> {
        self.constraints
            .assign_mvar(&mut self.mvars, id, value, justification)
    }

    /// Compose expression and universe substitution, in that order: an assigned
    /// expression may introduce universe metavariables not present in its input.
    pub fn instantiate_expr(&self, expr: &Expr) -> Result<Expr, UniverseInstantiationError> {
        self.universes
            .instantiate_expr(&self.mvars.instantiate(expr))
    }

    pub fn take_exposed_candidate(&mut self) -> Option<ExposedCandidate> {
        self.exposed_candidate.take()
    }

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
            snapshot: Box::new(self.clone()),
        }
    }

    pub fn child_txn(&self) -> ElabTxn {
        let mut child = self.clone();
        child.seed = self.seed.wrapping_mul(6364136223846793005).wrapping_add(1);
        child
    }

    /// Fork into N deterministic alternative child transactions.
    pub fn fork(&self, count: usize) -> Vec<ElabTxn> {
        let mut forks = Vec::with_capacity(count);
        let mut current_seed = self.seed;
        for i in 0..count {
            current_seed = current_seed
                .wrapping_mul(6364136223846793005)
                .wrapping_add((i as u64) + 1);
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

    /// Resolve a child against an unchanged semantic parent. Audit records and
    /// already-spent heartbeats may grow between sibling attempts. A resource
    /// failure still charges the reported work, but publishes no child state.
    pub fn commit_outcome(
        &mut self,
        checkpoint: &TxnCheckpoint,
        child: ElabTxn,
        outcome: TxnOutcome,
    ) -> Result<Option<Expr>, &'static str> {
        self.verify_no_state_leaks(checkpoint)?;
        let base = &checkpoint.snapshot;
        if matches!(&outcome, TxnOutcome::CommitAll)
            && !child
                .decisions
                .records()
                .starts_with(base.decisions.records())
        {
            return Err("child replaced the inherited decision journal");
        }
        self.charge_child_work(&base.budget, &child.budget)?;
        if child.budget.current_rec_depth != base.budget.current_rec_depth {
            return Err("child left an unbalanced elaboration recursion depth");
        }
        match outcome {
            TxnOutcome::CommitAll => {
                for record in &child.decisions.records()[base.decisions.len()..] {
                    self.decisions.record(record.clone());
                }
                self.env = child.env;
                self.lctx = child.lctx;
                self.mvars = child.mvars;
                self.universes = child.universes;
                self.constraints = child.constraints;
                self.messages = child.messages;
                self.info_tree = child.info_tree;
                self.options = child.options;
                self.seed = child.seed;
                self.exposed_candidate = child.exposed_candidate;
                Ok(None)
            }
            TxnOutcome::CommitDiagnosticsOnly => {
                self.messages = child.messages;
                self.info_tree = child.info_tree;
                self.decisions.record(DecisionRecord::TransactionRollback {
                    branch_id: 0,
                    reason: "commit_diagnostics_only".to_string(),
                });
                Ok(None)
            }
            TxnOutcome::Rollback => {
                self.decisions.record(DecisionRecord::TransactionRollback {
                    branch_id: 0,
                    reason: "explicit_rollback".to_string(),
                });
                Ok(None)
            }
            TxnOutcome::ExposeCandidate {
                candidate,
                obligations,
            } => {
                self.exposed_candidate = Some(ExposedCandidate {
                    expression: candidate.clone(),
                    obligations,
                    env: child.env,
                    lctx: child.lctx,
                    mvars: child.mvars,
                    universes: child.universes,
                    constraints: child.constraints,
                    options: child.options,
                    seed: child.seed,
                });
                Ok(Some(candidate))
            }
            TxnOutcome::Fork { alternatives_count } => {
                self.decisions.record(DecisionRecord::TransactionFork {
                    branch_id: 0,
                    num_alternatives: alternatives_count,
                });
                Ok(None)
            }
        }
    }

    fn charge_child_work(
        &mut self,
        base: &ElabBudget,
        child: &ElabBudget,
    ) -> Result<(), &'static str> {
        if self.budget.heartbeats_consumed < base.heartbeats_consumed {
            return Err("parent heartbeat accounting moved backwards");
        }
        let spent = child
            .heartbeats_consumed
            .checked_sub(base.heartbeats_consumed)
            .ok_or("child heartbeat accounting moved backwards")?;
        let total = self.budget.heartbeats_consumed.checked_add(spent);
        self.budget.heartbeats_consumed = total.unwrap_or(u64::MAX);
        let total = total.ok_or("heartbeat counter overflow")?;
        if self.budget.max_heartbeats > 0 && total > self.budget.max_heartbeats {
            return Err("max heartbeats exceeded");
        }
        Ok(())
    }

    /// Compare semantic values and indexes, not merely their cardinalities.
    pub fn verify_no_term_leaks(&self, checkpoint: &TxnCheckpoint) -> Result<(), &'static str> {
        let base = &checkpoint.snapshot;
        if self.mvars.decls() != base.mvars.decls() {
            return Err("leak detected: mvar decls modified after rollback");
        }
        if self.mvars.assignments() != base.mvars.assignments() {
            return Err("leak detected: mvar assignments modified after rollback");
        }
        if self.mvars != base.mvars {
            return Err("leak detected: mvar dependencies modified after rollback");
        }
        if self.universes != base.universes {
            return Err("leak detected: uvar assignments modified after rollback");
        }
        if self.lctx != base.lctx {
            return Err("leak detected: local context modified after rollback");
        }
        if self.constraints != base.constraints {
            return Err("leak detected: constraints modified after rollback");
        }
        if self.env != base.env {
            return Err("leak detected: environment modified after rollback");
        }
        if self.options != base.options {
            return Err("leak detected: options modified after rollback");
        }
        if self.seed != base.seed {
            return Err("leak detected: deterministic seed modified after rollback");
        }
        if self.budget.max_heartbeats != base.budget.max_heartbeats
            || self.budget.max_rec_depth != base.budget.max_rec_depth
            || self.budget.current_rec_depth != base.budget.current_rec_depth
        {
            return Err(
                "leak detected: resource policy or recursion scope modified after rollback",
            );
        }
        Ok(())
    }

    /// Audit all rollback-sensitive products. Spent work and append-only audit
    /// events intentionally survive rollback; inherited journal entries may not
    /// be rewritten or removed.
    pub fn verify_no_state_leaks(&self, checkpoint: &TxnCheckpoint) -> Result<(), &'static str> {
        self.verify_no_term_leaks(checkpoint)?;
        let base = &checkpoint.snapshot;
        if self.messages != base.messages {
            return Err("leak detected: messages modified after rollback");
        }
        if self.info_tree != base.info_tree {
            return Err("leak detected: info tree modified after rollback");
        }
        if self.exposed_candidate != base.exposed_candidate {
            return Err("leak detected: exposed candidate modified after rollback");
        }
        if !self
            .decisions
            .records()
            .starts_with(base.decisions.records())
        {
            return Err("leak detected: inherited decision journal modified after rollback");
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::mvar::MetavarKind;
    use crate::seed::bootstrap_nat_environment;
    use fln_core::level::{LMVarId, Level};
    use fln_core::name::Name;
    use fln_core::options::DataValue;
    use fln_kernel::verdict::Budget;

    fn transaction() -> ElabTxn {
        let env = bootstrap_nat_environment(Budget::for_stack_bytes(1024 * 1024)).unwrap();
        ElabTxn::new(env, KVMap::new(), 42)
    }

    fn declare(txn: &mut ElabTxn, name: &str) -> MVarId {
        let id = MVarId(Name::from_components([name]));
        txn.mvars.declare(
            id.clone(),
            id.0.clone(),
            Expr::sort(Level::one()),
            LocalContext::new(),
            MetavarKind::Natural,
            0,
            None,
        );
        id
    }

    #[test]
    fn same_size_universe_replacement_is_not_a_clean_rollback() {
        let mut txn = transaction();
        let u = LMVarId(Name::from_components(["u"]));
        txn.universes.assign(u.clone(), Level::zero());
        let cp = txn.checkpoint();
        txn.universes.assign(u, Level::one());
        assert_eq!(txn.universes.len(), cp.uvar_assignments_count);
        assert_eq!(
            txn.verify_no_term_leaks(&cp),
            Err("leak detected: uvar assignments modified after rollback"),
        );
    }

    #[test]
    fn changing_only_dependency_edges_is_detected() {
        let mut txn = transaction();
        let a = declare(&mut txn, "a");
        let b = declare(&mut txn, "b");
        let cp = txn.checkpoint();
        txn.mvars.register_reader(a, b);
        assert_eq!(txn.mvars.len(), cp.mvar_decls_count);
        assert_eq!(
            txn.verify_no_term_leaks(&cp),
            Err("leak detected: mvar dependencies modified after rollback"),
        );
    }

    #[test]
    fn sibling_rollbacks_accumulate_work_instead_of_refunding_it() {
        let mut txn = transaction();
        txn.budget.heartbeats_consumed = 10;
        let cp = txn.checkpoint();
        let mut first = txn.child_txn();
        let mut second = txn.child_txn();
        first.budget.heartbeats_consumed = 13;
        second.budget.heartbeats_consumed = 17;
        txn.commit_outcome(&cp, first, TxnOutcome::Rollback)
            .unwrap();
        txn.commit_outcome(&cp, second, TxnOutcome::Rollback)
            .unwrap();
        assert_eq!(txn.budget.heartbeats_consumed, 20);
        assert_eq!(txn.decisions.len(), 2);
        txn.verify_no_state_leaks(&cp).unwrap();
    }

    #[test]
    fn commit_all_preserves_options_seed_and_prior_rollback_events() {
        let mut txn = transaction();
        let cp = txn.checkpoint();
        let rejected = txn.child_txn();
        let mut accepted = txn.child_txn();
        let key = Name::from_components(["trace", "test"]);
        accepted
            .options
            .insert(key.clone(), DataValue::OfBool(true));
        accepted.decisions.record(DecisionRecord::TransactionFork {
            branch_id: 1,
            num_alternatives: 2,
        });
        let seed = accepted.seed;
        txn.commit_outcome(&cp, rejected, TxnOutcome::Rollback)
            .unwrap();
        txn.commit_outcome(&cp, accepted, TxnOutcome::CommitAll)
            .unwrap();
        assert!(txn.options.get_bool(&key, false));
        assert_eq!(txn.seed, seed);
        assert_eq!(txn.decisions.len(), 2);
        assert!(matches!(
            txn.decisions.records()[0],
            DecisionRecord::TransactionRollback { .. }
        ));
        assert!(matches!(
            txn.decisions.records()[1],
            DecisionRecord::TransactionFork { .. }
        ));
    }

    #[test]
    fn a_stale_parent_is_not_overwritten_by_a_child_commit() {
        let mut txn = transaction();
        let cp = txn.checkpoint();
        let child = txn.child_txn();
        txn.options
            .insert(Name::from_components(["changed"]), DataValue::OfNat(7));
        let before = txn.clone();
        assert!(
            txn.commit_outcome(&cp, child, TxnOutcome::CommitAll)
                .is_err()
        );
        assert_eq!(txn, before);
    }

    #[test]
    fn exposed_holes_keep_their_child_context_without_publishing_it() {
        let mut txn = transaction();
        let cp = txn.checkpoint();
        let mut child = txn.child_txn();
        let hole = declare(&mut child, "child_only");
        let expression = Expr::mvar(hole.clone());
        assert_eq!(
            txn.commit_outcome(
                &cp,
                child,
                TxnOutcome::ExposeCandidate {
                    candidate: expression.clone(),
                    obligations: vec![hole.clone()],
                },
            )
            .unwrap(),
            Some(expression.clone()),
        );
        assert!(!txn.mvars.is_declared(&hole));
        let exposed = txn.take_exposed_candidate().unwrap();
        assert_eq!(exposed.obligations, vec![hole.clone()]);
        assert!(exposed.mvars.is_declared(&hole));
        assert_eq!(exposed.instantiate_expr().unwrap(), expression);
        assert!(txn.take_exposed_candidate().is_none());
        txn.verify_no_state_leaks(&cp).unwrap();
    }

    #[test]
    fn assignment_resumes_obligations_inside_the_child_only() {
        let mut txn = transaction();
        let hole = declare(&mut txn, "hole");
        let waiting = txn.postpone(
            ConstraintKind::HasType {
                expr: Expr::mvar(hole.clone()),
                expected_type: Expr::sort(Level::one()),
            },
            0,
        );
        let cp = txn.checkpoint();
        let mut child = txn.child_txn();
        let ready = child
            .assign_mvar(
                hole.clone(),
                Expr::sort(Level::zero()),
                AssignmentJustification::DirectDefEq,
            )
            .unwrap();
        assert_eq!(ready.len(), 1);
        assert_eq!(ready[0].id, waiting);
        assert!(child.constraints.is_empty());
        txn.commit_outcome(&cp, child, TxnOutcome::Rollback)
            .unwrap();
        assert!(!txn.mvars.is_assigned(&hole));
        assert!(txn.constraints.constraints().contains_key(&waiting));
    }

    #[test]
    fn expression_assignment_is_expanded_before_universe_assignment() {
        let mut txn = transaction();
        let hole = declare(&mut txn, "hole");
        let u = LMVarId(Name::from_components(["u"]));
        txn.assign_mvar(
            hole.clone(),
            Expr::sort(Level::mvar(u.clone())),
            AssignmentJustification::DirectDefEq,
        )
        .unwrap();
        txn.universes.assign(u, Level::one());
        assert_eq!(
            txn.instantiate_expr(&Expr::mvar(hole)).unwrap(),
            Expr::sort(Level::one())
        );
    }

    #[test]
    fn budget_exhaustion_charges_work_but_publishes_no_child_state() {
        let mut txn = transaction();
        txn.budget.max_heartbeats = 1;
        let cp = txn.checkpoint();
        let mut child = txn.child_txn();
        let hole = declare(&mut child, "child_only");
        child.budget.heartbeats_consumed = 2;
        assert_eq!(
            txn.commit_outcome(&cp, child, TxnOutcome::CommitAll),
            Err("max heartbeats exceeded"),
        );
        assert_eq!(txn.budget.heartbeats_consumed, 2);
        assert!(!txn.mvars.is_declared(&hole));
        assert_eq!(txn.seed, 42);
        txn.verify_no_state_leaks(&cp).unwrap();
    }

    #[test]
    fn saturating_the_heartbeat_counter_is_not_success() {
        let mut budget = ElabBudget::new(0, 512);
        budget.heartbeats_consumed = u64::MAX;
        assert_eq!(budget.check_heartbeat(), Err("heartbeat counter overflow"));
        assert_eq!(budget.heartbeats_consumed, u64::MAX);
    }
}
