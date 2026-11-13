//! Constraint queue and postponed obligations for Athanor (plan §10.1, §10.2).
//!
//! Models defeq constraints, typing obligations, typeclass synthesis goals,
//! and delayed assignments with deterministic, targeted wake-up on assignment.

mod dependencies;
pub mod unify;

use self::unify::{
    DelayedConstraint, TypingConstraint, UnificationBudget, UnificationError, UnificationReport,
};
use crate::lctx::LocalContext;
use crate::mvar::{AssignmentJustification, MetavarError, MetavarStore};
use crate::txn::ElabTxn;
use fln_core::expr::{Expr, FVarId, MVarId};
use std::collections::{BTreeSet, HashMap, HashSet};
use std::sync::Arc;

/// Unique identifier for a postponed constraint.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ConstraintId(pub u64);

/// The kind of postponed constraint / obligation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConstraintKind {
    DefEq {
        lhs: Expr,
        rhs: Expr,
    },
    HasType {
        expr: Expr,
        expected_type: Expr,
    },
    SynthInstance {
        class: Expr,
        mvar: MVarId,
    },
    DelayedAssign {
        mvar: MVarId,
        fvars: Vec<FVarId>,
        val: Expr,
    },
}

impl ConstraintKind {
    /// Unsolved inputs under the current assignment graph. Synthesis and
    /// delayed-assignment targets are outputs, not blockers on themselves;
    /// their declared types and local contexts are inputs.
    pub fn dependencies(&self, store: &MetavarStore) -> HashSet<MVarId> {
        dependencies::reads(self, store, None, &HashSet::new())
    }

    /// Include the retained telescope and transitive metavariable type/context
    /// edges. Synthesis and delayed targets remain outputs, not self-blockers.
    pub fn dependencies_in_context(
        &self,
        store: &MetavarStore,
        locals: &LocalContext,
    ) -> HashSet<MVarId> {
        dependencies::reads(self, store, Some(locals), &HashSet::new())
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Constraint {
    pub id: ConstraintId,
    pub kind: ConstraintKind,
    pub reads_mvars: HashSet<MVarId>,
    pub depth: u32,
    /// The lexical scope at suspension, including an explicitly empty scope.
    /// Raw queue producers may leave this absent to request the resumer's
    /// context; `ElabTxn::postpone` always captures it. Sharing the immutable
    /// snapshot keeps queue/transaction forks from copying its declarations.
    pub local_context: Option<Arc<LocalContext>>,
    /// Conservative dynamic-read marker: when `true`, the obligation's dynamic
    /// read set could not be bounded statically, so any metavariable assignment
    /// wakes it and `take_ready` holds it until its reads are narrowed.
    pub reads_unknown: bool,
}

impl Constraint {
    /// Inputs include the saved context: K1 checks its dependent local types
    /// and let values even when the obligation's terms themselves are ground.
    pub fn dependencies(&self, store: &MetavarStore) -> HashSet<MVarId> {
        dependencies::reads(
            &self.kind,
            store,
            self.local_context.as_deref(),
            &HashSet::new(),
        )
    }
}

/// Hash maps are lookup indexes only: every returned batch is ordered by the
/// monotone constraint identity, independently of hash seeds and input order.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ConstraintQueue {
    next_id: u64,
    constraints: HashMap<ConstraintId, Constraint>,
    mvar_to_constraints: HashMap<MVarId, HashSet<ConstraintId>>,
    unknown_reader_constraints: BTreeSet<ConstraintId>,
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
    pub fn unknown_reader_count(&self) -> usize {
        self.unknown_reader_constraints.len()
    }

    /// Enqueue with an explicit observed-read signature. Use `enqueue_inferred`
    /// when the obligation's terms are the complete signature.
    pub fn enqueue(
        &mut self,
        kind: ConstraintKind,
        reads_mvars: HashSet<MVarId>,
        depth: u32,
    ) -> ConstraintId {
        self.enqueue_with_context(kind, reads_mvars, depth, None, false)
    }

    /// Enqueue an obligation whose dynamic read set is conservatively unknown:
    /// any subsequent metavariable assignment will wake it.
    pub fn enqueue_conservative(
        &mut self,
        kind: ConstraintKind,
        reads_mvars: HashSet<MVarId>,
        depth: u32,
    ) -> ConstraintId {
        self.enqueue_with_context(kind, reads_mvars, depth, None, true)
    }

    fn enqueue_with_context(
        &mut self,
        kind: ConstraintKind,
        reads_mvars: HashSet<MVarId>,
        depth: u32,
        local_context: Option<Arc<LocalContext>>,
        reads_unknown: bool,
    ) -> ConstraintId {
        let id = ConstraintId(self.next_id);
        self.next_id += 1;
        for mvar in &reads_mvars {
            self.mvar_to_constraints
                .entry(mvar.clone())
                .or_default()
                .insert(id);
        }
        if reads_unknown {
            self.unknown_reader_constraints.insert(id);
        }
        self.constraints.insert(
            id,
            Constraint {
                id,
                kind,
                reads_mvars,
                depth,
                local_context,
                reads_unknown,
            },
        );
        id
    }

    pub fn enqueue_inferred(
        &mut self,
        kind: ConstraintKind,
        store: &MetavarStore,
        depth: u32,
    ) -> ConstraintId {
        let reads = kind.dependencies(store);
        self.enqueue(kind, reads, depth)
    }

    /// Suspend under an immutable lexical snapshot. Wake-ups carry this same
    /// scope, independently of later entry into or exit from sibling binders.
    pub fn enqueue_scoped(
        &mut self,
        kind: ConstraintKind,
        store: &MetavarStore,
        locals: &LocalContext,
        depth: u32,
    ) -> ConstraintId {
        let local_context = Some(Arc::new(locals.clone()));
        let row = Constraint {
            id: ConstraintId(self.next_id),
            kind,
            reads_mvars: HashSet::new(),
            depth,
            local_context,
            reads_unknown: false,
        };
        let reads = row.dependencies(store);
        self.enqueue_with_context(row.kind, reads, depth, row.local_context, false)
    }

    /// Suspend under an immutable lexical snapshot while marking dynamic reads
    /// conservatively unknown so any metavariable assignment wakes the row.
    pub fn enqueue_conservative_scoped(
        &mut self,
        kind: ConstraintKind,
        store: &MetavarStore,
        locals: &LocalContext,
        depth: u32,
    ) -> ConstraintId {
        let local_context = Some(Arc::new(locals.clone()));
        let row = Constraint {
            id: ConstraintId(self.next_id),
            kind,
            reads_mvars: HashSet::new(),
            depth,
            local_context,
            reads_unknown: true,
        };
        let reads = row.dependencies(store);
        self.enqueue_with_context(row.kind, reads, depth, row.local_context, true)
    }

    /// Mark an existing queued obligation as conservatively reading unknown metavariables.
    pub fn mark_reads_unknown(&mut self, id: ConstraintId) -> bool {
        let Some(row) = self.constraints.get_mut(&id) else {
            return false;
        };
        row.reads_unknown = true;
        self.unknown_reader_constraints.insert(id);
        true
    }

    /// Update observed reads without changing identity or scheduling priority,
    /// clearing any conservative `reads_unknown` marker. Missing IDs leave the queue unchanged.
    pub fn update_reads(&mut self, id: ConstraintId, reads: HashSet<MVarId>) -> bool {
        let Some(mut constraint) = self.remove(&id) else {
            return false;
        };
        for mvar in &reads {
            self.mvar_to_constraints
                .entry(mvar.clone())
                .or_default()
                .insert(id);
        }
        constraint.reads_mvars = reads;
        constraint.reads_unknown = false;
        self.constraints.insert(id, constraint);
        true
    }

    /// Refusals leave both store and queue untouched. Resumed obligations are
    /// candidates for rechecking, not solved proofs.
    pub fn assign_mvar(
        &mut self,
        store: &mut MetavarStore,
        id: MVarId,
        value: Expr,
        justification: AssignmentJustification,
    ) -> Result<Vec<Constraint>, MetavarError> {
        let mut affected = store.assign(id.clone(), value, justification)?;
        affected.insert(id);
        Ok(self.wake_up_for_mvars(affected.iter()))
    }

    pub fn wake_up_for_mvar(&mut self, mvar: &MVarId) -> Vec<Constraint> {
        self.wake_up_for_mvars(std::iter::once(mvar))
    }

    /// Extract the union in stable identity order, returning each row once.
    pub fn wake_up_for_mvars<'a>(
        &mut self,
        mvars: impl IntoIterator<Item = &'a MVarId>,
    ) -> Vec<Constraint> {
        let mut ids = BTreeSet::new();
        let mut any_mvar = false;
        for mvar in mvars {
            any_mvar = true;
            if let Some(readers) = self.mvar_to_constraints.get(mvar) {
                ids.extend(readers.iter().copied());
            }
        }
        if any_mvar {
            ids.extend(self.unknown_reader_constraints.iter().copied());
        }
        ids.into_iter().filter_map(|id| self.remove(&id)).collect()
    }

    /// Extract obligations with no unresolved inputs and known read sets; this does not decide them.
    pub fn take_ready(&mut self) -> Vec<Constraint> {
        let ids: BTreeSet<_> = self
            .constraints
            .values()
            .filter(|row| row.reads_mvars.is_empty() && !row.reads_unknown)
            .map(|row| row.id)
            .collect();
        ids.into_iter().filter_map(|id| self.remove(&id)).collect()
    }

    pub fn remove(&mut self, id: &ConstraintId) -> Option<Constraint> {
        let constraint = self.constraints.remove(id)?;
        self.unknown_reader_constraints.remove(id);
        for mvar in &constraint.reads_mvars {
            let empty = self.mvar_to_constraints.get_mut(mvar).is_some_and(|set| {
                set.remove(id);
                set.is_empty()
            });
            if empty {
                self.mvar_to_constraints.remove(mvar);
            }
        }
        Some(constraint)
    }
}

/// Selection errors are distinct from unification nonanswers and kernel vetoes.
#[derive(Debug)]
pub enum ConstraintSolveError {
    Missing(ConstraintId),
    /// Detached input must not replace a row still owned by the queue.
    AlreadyQueued(ConstraintId),
    /// A detached batch contains two competing versions of the same identity.
    DuplicateResumption(ConstraintId),
    NotDefEq(ConstraintId),
    UnsupportedKind(ConstraintId),
    Depth {
        id: ConstraintId,
        observed: u32,
        allowed: u32,
    },
    Unification(UnificationError),
}

impl std::fmt::Display for ConstraintSolveError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Missing(id) => write!(f, "constraint {} is not queued", id.0),
            Self::AlreadyQueued(id) => write!(f, "constraint {} is already queued", id.0),
            Self::DuplicateResumption(id) => {
                write!(f, "constraint {} occurs twice in a resumed batch", id.0)
            }
            Self::NotDefEq(id) => write!(
                f,
                "constraint {} is not a definitional-equality obligation",
                id.0
            ),
            Self::UnsupportedKind(id) => {
                write!(
                    f,
                    "constraint {} is not owned by the native equation solver",
                    id.0
                )
            }
            Self::Depth {
                id,
                observed,
                allowed,
            } => write!(f, "constraint {} depth {observed} exceeds {allowed}", id.0),
            Self::Unification(error) => write!(f, "{error}"),
        }
    }
}
impl std::error::Error for ConstraintSolveError {}

#[derive(Debug)]
pub struct ConstraintSolveReport {
    /// Only selected, discharged rows, in stable order. A checked HasType row
    /// does not solve its value's residual holes; those remain in the report.
    pub solved: Vec<ConstraintId>,
    /// Awakened rows here still require processing; they are not counted solved.
    pub unification: UnificationReport,
}

impl ElabTxn {
    /// Execute rows detached by `assign_mvar`, `take_ready`, or an earlier
    /// solver report, keeping their original identities and lexical scopes.
    /// This is the same native solver, not a second scheduler or a proof path.
    ///
    /// The caller retains the borrowed rows on failure; no restored rows,
    /// assignments or wake-ups are published. On success only the selected
    /// rows are discharged, and further wake-ups are returned for the next
    /// explicit batch. No fresh constraint IDs are allocated. IDs must have
    /// been issued by this queue, must be unique, and must not still be queued.
    pub fn resume_constraints_with(
        &mut self,
        rows: &[Constraint],
        budget: UnificationBudget,
        cancelled: &dyn Fn() -> bool,
    ) -> Result<ConstraintSolveReport, ConstraintSolveError> {
        let cancelled_error = || ConstraintSolveError::Unification(UnificationError::Cancelled);
        if cancelled() {
            return Err(cancelled_error());
        }
        let mut copied = rows.len();
        let mut selected = BTreeSet::new();
        for row in rows {
            if cancelled() {
                return Err(cancelled_error());
            }
            copied = copied
                .saturating_add(row.reads_mvars.len())
                .saturating_add(row.local_context.as_deref().map_or(0, LocalContext::len));
            if copied > budget.max_visited_nodes {
                return Err(ConstraintSolveError::Unification(
                    UnificationError::NodeLimit {
                        limit: budget.max_visited_nodes,
                    },
                ));
            }
            if row.id.0 >= self.constraints.next_id {
                return Err(ConstraintSolveError::Missing(row.id));
            }
            if !selected.insert(row.id) {
                return Err(ConstraintSolveError::DuplicateResumption(row.id));
            }
            if self.constraints.constraints.contains_key(&row.id) {
                return Err(ConstraintSolveError::AlreadyQueued(row.id));
            }
        }
        let mut trial = self.clone();
        for row in rows {
            for mvar in &row.reads_mvars {
                if cancelled() {
                    return Err(cancelled_error());
                }
                trial
                    .constraints
                    .mvar_to_constraints
                    .entry(mvar.clone())
                    .or_default()
                    .insert(row.id);
            }
            if row.reads_unknown {
                trial.constraints.unknown_reader_constraints.insert(row.id);
            }
            trial.constraints.constraints.insert(row.id, row.clone());
        }
        let ids: Vec<_> = selected.into_iter().collect();
        let result = trial.solve_constraints_with(&ids, budget, cancelled);
        self.budget.heartbeats_consumed = trial.budget.heartbeats_consumed;
        let report = result?;
        if cancelled() {
            return Err(cancelled_error());
        }
        self.mvars = trial.mvars;
        self.universes = trial.universes;
        self.constraints = trial.constraints;
        Ok(report)
    }

    /// Solve selected queued DefEq obligations as one atomic batch. Callers may
    /// pass IDs in any order or repeat them. Missing, non-DefEq or deeper rows
    /// refuse the selection before mutation. A later solver nonanswer preserves
    /// the original queue and assignments while retaining work accounting.
    pub fn solve_defeq_constraints_with(
        &mut self,
        ids: &[ConstraintId],
        budget: UnificationBudget,
        cancelled: &dyn Fn() -> bool,
    ) -> Result<ConstraintSolveReport, ConstraintSolveError> {
        self.solve_selected_constraints_with(ids, budget, cancelled, true)
    }

    /// Solve a mixed DefEq/HasType/DelayedAssign batch with one shared budget
    /// and one atomic publication. Typing rows generate necessary equations, then K1 checks
    /// each original term under its local context and typed residual holes.
    /// SynthInstance remains Synod's responsibility, not a unifier verdict.
    /// Delayed rows assign only their designated target; their explicit
    /// arguments must be distinct, in-scope parameter locals, not local lets.
    /// Each scoped row uses its suspension context, not the caller's current
    /// binders. Explicitly unscoped raw queue rows use the caller's context.
    pub fn solve_constraints_with(
        &mut self,
        ids: &[ConstraintId],
        budget: UnificationBudget,
        cancelled: &dyn Fn() -> bool,
    ) -> Result<ConstraintSolveReport, ConstraintSolveError> {
        self.solve_selected_constraints_with(ids, budget, cancelled, false)
    }

    fn solve_selected_constraints_with(
        &mut self,
        ids: &[ConstraintId],
        budget: UnificationBudget,
        cancelled: &dyn Fn() -> bool,
        defeq_only: bool,
    ) -> Result<ConstraintSolveReport, ConstraintSolveError> {
        if cancelled() {
            return Err(ConstraintSolveError::Unification(
                UnificationError::Cancelled,
            ));
        }
        if ids.len() > budget.max_visited_nodes {
            return Err(ConstraintSolveError::Unification(
                UnificationError::NodeLimit {
                    limit: budget.max_visited_nodes,
                },
            ));
        }
        let selected: BTreeSet<_> = ids.iter().copied().collect();
        let mut equations = Vec::new();
        let mut typings = Vec::new();
        let mut delayed = Vec::new();
        let mut delayed_arguments = 0usize;
        let mut context_nodes = 0usize;
        for id in &selected {
            if cancelled() {
                return Err(ConstraintSolveError::Unification(
                    UnificationError::Cancelled,
                ));
            }
            let row = self
                .constraints
                .constraints()
                .get(id)
                .ok_or(ConstraintSolveError::Missing(*id))?;
            if row.depth > budget.max_metavar_depth {
                return Err(ConstraintSolveError::Depth {
                    id: *id,
                    observed: row.depth,
                    allowed: budget.max_metavar_depth,
                });
            }
            if defeq_only && !matches!(row.kind, ConstraintKind::DefEq { .. }) {
                return Err(ConstraintSolveError::NotDefEq(*id));
            }
            let locals = row.local_context.as_deref().unwrap_or(&self.lctx);
            context_nodes = context_nodes.saturating_add(locals.len());
            if context_nodes > budget.max_visited_nodes {
                return Err(ConstraintSolveError::Unification(
                    UnificationError::NodeLimit {
                        limit: budget.max_visited_nodes,
                    },
                ));
            }
            match &row.kind {
                ConstraintKind::DefEq { lhs, rhs } => {
                    equations.push((lhs.clone(), rhs.clone(), locals.clone()));
                }
                ConstraintKind::HasType {
                    expr,
                    expected_type,
                } => typings.push(TypingConstraint {
                    id: *id,
                    expr: expr.clone(),
                    expected_type: expected_type.clone(),
                    depth: row.depth,
                    locals: locals.clone(),
                }),
                ConstraintKind::DelayedAssign { mvar, fvars, val } => {
                    delayed_arguments = delayed_arguments.saturating_add(fvars.len());
                    if delayed_arguments > budget.max_visited_nodes {
                        return Err(ConstraintSolveError::Unification(
                            UnificationError::NodeLimit {
                                limit: budget.max_visited_nodes,
                            },
                        ));
                    }
                    delayed.push(DelayedConstraint {
                        id: *id,
                        mvar: mvar.clone(),
                        fvars: fvars.clone(),
                        val: val.clone(),
                        depth: row.depth,
                        locals: locals.clone(),
                    });
                }
                _ => return Err(ConstraintSolveError::UnsupportedKind(*id)),
            }
        }
        let mut trial = self.clone();
        for id in &selected {
            trial.constraints.remove(id);
        }
        let result =
            trial.unify_obligations_with(&equations, &typings, &delayed, budget, cancelled);
        self.budget.heartbeats_consumed = trial.budget.heartbeats_consumed;
        let unification = result.map_err(ConstraintSolveError::Unification)?;
        if cancelled() {
            return Err(ConstraintSolveError::Unification(
                UnificationError::Cancelled,
            ));
        }
        self.mvars = trial.mvars;
        self.universes = trial.universes;
        self.constraints = trial.constraints;
        Ok(ConstraintSolveReport {
            solved: selected.into_iter().collect(),
            unification,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::unify::UnificationDeferred;
    use super::*;
    use crate::lctx::LocalContext;
    use crate::mvar::MetavarKind;
    use fln_core::expr::{BinderInfo, ExprNode, Literal, NatLit};
    use fln_core::level::Level;
    use fln_core::name::Name;
    use fln_core::options::KVMap;
    use fln_core::outcome::Outcome;
    use fln_kernel::verdict::Verdict;

    fn mvar(name: &str) -> MVarId {
        MVarId(Name::from_components([name]))
    }
    fn declare(store: &mut MetavarStore, id: &MVarId) {
        store.declare(
            id.clone(),
            id.0.clone(),
            Expr::sort(Level::one()),
            LocalContext::new(),
            MetavarKind::Natural,
            0,
            None,
        );
    }
    fn ground() -> ConstraintKind {
        ConstraintKind::DefEq {
            lhs: Expr::sort(Level::zero()),
            rhs: Expr::sort(Level::zero()),
        }
    }

    #[test]
    fn wake_batches_are_ordered_deduplicated_and_fully_deindexed() {
        let a = mvar("a");
        let b = mvar("b");
        let unrelated = mvar("unrelated");
        let mut queue = ConstraintQueue::new();
        let first = queue.enqueue(ground(), HashSet::from([b.clone()]), 0);
        let second = queue.enqueue(ground(), HashSet::from([a.clone()]), 0);
        let both = queue.enqueue(ground(), HashSet::from([a.clone(), b.clone()]), 0);
        let waiting = queue.enqueue(ground(), HashSet::from([unrelated.clone()]), 0);
        let mut reverse = queue.clone();
        let ready = queue.wake_up_for_mvars([&a, &b, &a]);
        assert_eq!(ready, reverse.wake_up_for_mvars([&b, &a]));
        assert_eq!(
            ready.iter().map(|row| row.id).collect::<Vec<_>>(),
            vec![first, second, both]
        );
        assert_eq!(queue.len(), 1);
        assert!(queue.constraints().contains_key(&waiting));
        assert!(queue.wake_up_for_mvars([&a, &b]).is_empty());
        assert_eq!(queue.mvar_to_constraints.len(), 1);
        assert!(queue.mvar_to_constraints.contains_key(&unrelated));
    }

    #[test]
    fn assignment_resumes_readers_of_an_already_assigned_alias() {
        let a = mvar("a");
        let b = mvar("b");
        let mut store = MetavarStore::new();
        declare(&mut store, &a);
        declare(&mut store, &b);
        store
            .assign(
                a.clone(),
                Expr::mvar(b.clone()),
                AssignmentJustification::DirectDefEq,
            )
            .unwrap();
        let mut queue = ConstraintQueue::new();
        let id = queue.enqueue(ground(), HashSet::from([a]), 0);
        let ready = queue
            .assign_mvar(
                &mut store,
                b,
                Expr::sort(Level::zero()),
                AssignmentJustification::DirectDefEq,
            )
            .unwrap();
        assert_eq!(ready.iter().map(|row| row.id).collect::<Vec<_>>(), vec![id]);
        assert!(queue.is_empty());
    }

    #[test]
    fn failed_assignment_changes_neither_store_nor_queue() {
        let a = mvar("a");
        let mut store = MetavarStore::new();
        declare(&mut store, &a);
        let mut queue = ConstraintQueue::new();
        queue.enqueue(ground(), HashSet::from([a.clone()]), 0);
        let before_store = store.clone();
        let before_queue = queue.clone();
        assert!(
            queue
                .assign_mvar(
                    &mut store,
                    a.clone(),
                    Expr::mdata(KVMap::new(), Expr::mvar(a)),
                    AssignmentJustification::DirectDefEq
                )
                .is_err()
        );
        assert_eq!(store, before_store);
        assert_eq!(queue, before_queue);
    }

    #[test]
    fn inferred_reads_follow_aliases_and_metadata() {
        let a = mvar("a");
        let b = mvar("b");
        let mut store = MetavarStore::new();
        declare(&mut store, &a);
        declare(&mut store, &b);
        store
            .assign(
                a.clone(),
                Expr::mvar(b.clone()),
                AssignmentJustification::DirectDefEq,
            )
            .unwrap();
        let mut queue = ConstraintQueue::new();
        let id = queue.enqueue_inferred(
            ConstraintKind::HasType {
                expr: Expr::mdata(KVMap::new(), Expr::mvar(a)),
                expected_type: Expr::sort(Level::one()),
            },
            &store,
            3,
        );
        assert_eq!(
            queue.constraints()[&id].reads_mvars,
            HashSet::from([b.clone()])
        );
        assert!(queue.take_ready().is_empty());
        assert_eq!(queue.wake_up_for_mvar(&b)[0].depth, 3);
    }

    #[test]
    fn a_synthesis_output_does_not_block_its_own_ready_obligation() {
        let target = mvar("goal");
        let mut store = MetavarStore::new();
        declare(&mut store, &target);
        let mut queue = ConstraintQueue::new();
        let id = queue.enqueue_inferred(
            ConstraintKind::SynthInstance {
                class: Expr::const_(Name::from_components(["TestClass"]), Vec::new()),
                mvar: target.clone(),
            },
            &store,
            0,
        );
        let ready = queue.take_ready();
        assert_eq!(ready.len(), 1);
        assert_eq!(ready[0].id, id);
        assert!(!store.is_assigned(&target));
        assert!(queue.is_empty());
    }

    #[test]
    fn reindexing_preserves_identity_and_removes_old_blockers() {
        let a = mvar("a");
        let b = mvar("b");
        let mut queue = ConstraintQueue::new();
        let id = queue.enqueue(ground(), HashSet::from([a.clone()]), 4);
        assert!(queue.update_reads(id, HashSet::from([b.clone()])));
        assert!(queue.wake_up_for_mvar(&a).is_empty());
        assert!(!queue.mvar_to_constraints.contains_key(&a));
        assert!(queue.update_reads(id, HashSet::new()));
        assert!(queue.wake_up_for_mvar(&b).is_empty());
        let ready = queue.take_ready();
        assert_eq!(ready.len(), 1);
        assert_eq!(ready[0].id, id);
        assert_eq!(ready[0].depth, 4);
        assert!(queue.mvar_to_constraints.is_empty());
        let before = queue.clone();
        assert!(!queue.update_reads(id, HashSet::from([a])));
        assert_eq!(queue, before);
    }

    fn solver_transaction() -> (ElabTxn, UnificationBudget, MVarId) {
        let budget =
            UnificationBudget::new(fln_kernel::verdict::Budget::for_stack_bytes(1024 * 1024));
        let env = crate::seed::bootstrap_nat_environment(budget.kernel).unwrap();
        let mut txn = ElabTxn::new(env, KVMap::new(), 19);
        let id = mvar("type_hole");
        declare(&mut txn.mvars, &id);
        (txn, budget, id)
    }

    fn nat() -> Expr {
        Expr::const_(Name::from_components(["Nat"]), vec![])
    }

    fn numeral(value: u64) -> Expr {
        Expr::lit(Literal::Nat(NatLit::from_u64(value)))
    }

    fn pi(domain: Expr, body: Expr) -> Expr {
        Expr::forall_e(
            Name::from_components(["argument"]),
            domain,
            body,
            BinderInfo::Default,
        )
    }

    fn scope_function(txn: &mut ElabTxn, type_: Expr, arguments: Option<usize>) -> MVarId {
        let id = mvar("scope_function");
        txn.mvars.declare(
            id.clone(),
            id.0.clone(),
            type_,
            txn.lctx.clone(),
            MetavarKind::Natural,
            0,
            None,
        );
        if let Some(arguments) = arguments {
            txn.mvars.set_scope_args(&id, arguments).unwrap();
        }
        id
    }

    fn lambda_parts(value: &Expr) -> (&Expr, &Expr) {
        let ExprNode::Lam {
            binder_type, body, ..
        } = value.node()
        else {
            panic!("expected a synthesized lambda: {value:?}");
        };
        (binder_type, body)
    }

    fn assert_solver_rollback(actual: &ElabTxn, before: &ElabTxn) {
        let mut semantic_state = actual.clone();
        semantic_state.budget = before.budget.clone();
        assert_eq!(&semantic_state, before);
        assert!(actual.budget.heartbeats_consumed > before.budget.heartbeats_consumed);
    }

    #[test]
    fn dependent_scope_suffixes_construct_checked_general_functions() {
        let (mut txn, budget, _) = solver_transaction();
        let function = scope_function(
            &mut txn,
            pi(Expr::sort(Level::one()), pi(Expr::bvar(0).unwrap(), nat())),
            Some(2),
        );
        let lhs = Expr::app(Expr::app(Expr::mvar(function.clone()), nat()), numeral(3));
        let report = txn.unify(&lhs, &numeral(7), budget).unwrap();
        assert_eq!(report.kernel_checks, 2);
        let value = txn.mvars.get_assigned_expr(&function).unwrap();
        let (domain, body) = lambda_parts(value);
        assert_eq!(domain, &Expr::sort(Level::one()));
        let (domain, body) = lambda_parts(body);
        assert_eq!(domain, &Expr::bvar(0).unwrap());
        assert_eq!(body, &numeral(7));
        assert!(!value.has_fvar());
        assert!(!value.has_loose_bvars());
        assert!(txn.lctx.is_empty());
    }

    #[test]
    fn dependent_scope_suffixes_keep_prefix_variables_and_repeated_arguments_separate() {
        let (mut txn, budget, _) = solver_transaction();
        let function = scope_function(
            &mut txn,
            pi(
                nat(),
                pi(
                    Expr::sort(Level::one()),
                    pi(Expr::sort(Level::one()), pi(Expr::bvar(0).unwrap(), nat())),
                ),
            ),
            Some(4),
        );
        let seed = FVarId(Name::from_components(["seed"]));
        let carrier = FVarId(Name::from_components(["A"]));
        let element = FVarId(Name::from_components(["element"]));
        txn.lctx
            .add_param(seed.clone(), seed.0.clone(), nat(), BinderInfo::Default);
        txn.lctx.add_param(
            carrier.clone(),
            carrier.0.clone(),
            Expr::sort(Level::one()),
            BinderInfo::Default,
        );
        txn.lctx.add_param(
            element.clone(),
            element.0.clone(),
            Expr::fvar(carrier.clone()),
            BinderInfo::Default,
        );
        let lhs = [
            Expr::fvar(seed.clone()),
            Expr::fvar(carrier.clone()),
            Expr::fvar(carrier),
            Expr::fvar(element),
        ]
        .into_iter()
        .fold(Expr::mvar(function.clone()), Expr::app);
        txn.unify(&lhs, &Expr::fvar(seed), budget).unwrap();
        let value = txn.mvars.get_assigned_expr(&function).unwrap();
        let (_, body) = lambda_parts(value);
        let (_, body) = lambda_parts(body);
        let (_, body) = lambda_parts(body);
        let (domain, body) = lambda_parts(body);
        assert_eq!(domain, &Expr::bvar(0).unwrap());
        assert_eq!(body, &Expr::bvar(3).unwrap());
        assert!(!value.has_fvar());
        assert!(!value.has_loose_bvars());
    }

    #[test]
    fn dependent_scope_suffixes_preserve_universe_parameters_and_binder_styles() {
        let (mut txn, budget, _) = solver_transaction();
        let universe = Level::param(Name::from_components(["u"]));
        let carrier = FVarId(Name::from_components(["carrier"]));
        let element = FVarId(Name::from_components(["element"]));
        txn.lctx.add_param(
            carrier.clone(),
            carrier.0.clone(),
            Expr::sort(universe.clone()),
            BinderInfo::Default,
        );
        txn.lctx.add_param(
            element.clone(),
            element.0.clone(),
            Expr::fvar(carrier.clone()),
            BinderInfo::Default,
        );
        let type_ = Expr::forall_e(
            Name::from_components(["A"]),
            Expr::sort(universe.clone()),
            Expr::forall_e(
                Name::from_components(["value"]),
                Expr::bvar(0).unwrap(),
                nat(),
                BinderInfo::Implicit,
            ),
            BinderInfo::StrictImplicit,
        );
        let function = scope_function(&mut txn, type_, Some(2));
        let locals = txn.lctx.clone();
        let lhs = Expr::app(
            Expr::app(Expr::mvar(function.clone()), Expr::fvar(carrier)),
            Expr::fvar(element),
        );
        txn.unify(&lhs, &numeral(7), budget).unwrap();
        assert_eq!(txn.lctx, locals);
        assert_eq!(
            txn.mvars.get_assigned_expr(&function),
            Some(&Expr::lam(
                Name::from_components(["A"]),
                Expr::sort(universe),
                Expr::lam(
                    Name::from_components(["value"]),
                    Expr::bvar(0).unwrap(),
                    numeral(7),
                    BinderInfo::Implicit,
                ),
                BinderInfo::StrictImplicit,
            )),
        );
    }

    #[test]
    fn dependent_scope_suffixes_constrain_the_applied_result_type() {
        let (mut txn, budget, _) = solver_transaction();
        let family = mvar("result_family");
        txn.mvars.declare(
            family.clone(),
            family.0.clone(),
            pi(Expr::sort(Level::one()), Expr::sort(Level::one())),
            txn.lctx.clone(),
            MetavarKind::Natural,
            0,
            None,
        );
        let carrier = FVarId(Name::from_components(["carrier"]));
        let element = FVarId(Name::from_components(["element"]));
        txn.lctx.add_param(
            carrier.clone(),
            carrier.0.clone(),
            Expr::sort(Level::one()),
            BinderInfo::Default,
        );
        txn.lctx.add_param(
            element.clone(),
            element.0.clone(),
            Expr::fvar(carrier.clone()),
            BinderInfo::Default,
        );
        // The actual carrier is in the function hole's context, but not the family's.
        // The result constraint must infer `family := fun _ => Nat` in that original scope.
        let function = scope_function(
            &mut txn,
            pi(
                Expr::sort(Level::one()),
                pi(
                    Expr::bvar(0).unwrap(),
                    Expr::app(Expr::mvar(family.clone()), Expr::bvar(1).unwrap()),
                ),
            ),
            Some(2),
        );
        let lhs = Expr::app(
            Expr::app(Expr::mvar(function.clone()), Expr::fvar(carrier)),
            Expr::fvar(element),
        );
        let report = txn.unify(&lhs, &numeral(7), budget).unwrap();
        let family_value = txn.mvars.get_assigned_expr(&family).unwrap();
        let (domain, body) = lambda_parts(family_value);
        assert_eq!(domain, &Expr::sort(Level::one()));
        assert_eq!(body, &nat());
        assert!(!family_value.has_fvar());
        assert!(report.expression_assignments.contains(&function));
        assert!(report.expression_assignments.contains(&family));
        assert!(report.kernel_checks >= 4);
    }

    #[test]
    fn dependent_scope_suffixes_require_an_exact_scope_argument_count() {
        for scope_args in [None, Some(1), Some(3)] {
            let (mut txn, budget, _) = solver_transaction();
            let function = scope_function(
                &mut txn,
                pi(Expr::sort(Level::one()), pi(Expr::bvar(0).unwrap(), nat())),
                scope_args,
            );
            let lhs = Expr::app(Expr::app(Expr::mvar(function), nat()), numeral(3));
            let before = txn.clone();
            assert!(matches!(
                txn.unify(&lhs, &numeral(7), budget),
                Err(UnificationError::Deferred(UnificationDeferred::NotAPattern)),
            ));
            assert_solver_rollback(&txn, &before);
        }
    }

    #[test]
    fn dependent_scope_suffixes_cannot_specialize_a_universal_result() {
        for (type_, arguments) in [
            (
                pi(Expr::sort(Level::one()), Expr::bvar(0).unwrap()),
                vec![nat()],
            ),
            (
                pi(
                    Expr::sort(Level::one()),
                    pi(Expr::bvar(0).unwrap(), Expr::bvar(1).unwrap()),
                ),
                vec![nat(), numeral(3)],
            ),
        ] {
            let (mut txn, budget, _) = solver_transaction();
            let function = scope_function(&mut txn, type_, Some(arguments.len()));
            let lhs = arguments
                .into_iter()
                .fold(Expr::mvar(function.clone()), Expr::app);
            let before = txn.clone();
            let error = txn.unify(&lhs, &numeral(7), budget).unwrap_err();
            let UnificationError::AssignmentCheck { id, outcome } = error else {
                panic!("the real kernel must veto the generalized assignment: {error:?}");
            };
            assert_eq!(id, function);
            assert!(matches!(
                *outcome,
                Outcome::Complete(Verdict::Rejected { .. })
            ));
            assert_solver_rollback(&txn, &before);
        }
    }

    #[test]
    fn dependent_scope_suffixes_roll_back_when_the_budget_ends() {
        let (mut txn, mut budget, _) = solver_transaction();
        let function = scope_function(
            &mut txn,
            pi(Expr::sort(Level::one()), pi(Expr::bvar(0).unwrap(), nat())),
            Some(2),
        );
        let lhs = Expr::app(Expr::app(Expr::mvar(function), nat()), numeral(3));
        let mut complete = txn.clone();
        let report = complete.unify(&lhs, &numeral(7), budget).unwrap();
        budget.max_steps = report.unifier_steps.checked_sub(1).unwrap();
        let before = txn.clone();
        assert!(matches!(
            txn.unify(&lhs, &numeral(7), budget),
            Err(UnificationError::StepLimit { .. }),
        ));
        assert_solver_rollback(&txn, &before);
    }

    #[test]
    fn queued_solver_distinguishes_solved_rows_from_awakened_obligations() {
        let (mut txn, budget, id) = solver_transaction();
        let solve = txn.postpone(
            ConstraintKind::DefEq {
                lhs: Expr::mvar(id.clone()),
                rhs: Expr::sort(Level::zero()),
            },
            0,
        );
        let wake = txn.postpone(
            ConstraintKind::HasType {
                expr: Expr::mvar(id.clone()),
                expected_type: Expr::sort(Level::one()),
            },
            0,
        );
        let untouched = txn.postpone(ground(), 0);
        let report = txn
            .solve_defeq_constraints_with(&[solve], budget, &|| false)
            .unwrap();
        assert_eq!(report.solved, vec![solve]);
        assert_eq!(
            report
                .unification
                .awakened
                .iter()
                .map(|row| row.id)
                .collect::<Vec<_>>(),
            vec![wake]
        );
        assert_eq!(txn.constraints.len(), 1);
        assert!(txn.constraints.constraints().contains_key(&untouched));
        assert!(txn.mvars.is_assigned(&id));
    }

    #[test]
    fn failed_queued_batch_keeps_original_ids_indexes_and_assignments() {
        let (mut txn, budget, id) = solver_transaction();
        let first = txn.postpone(
            ConstraintKind::DefEq {
                lhs: Expr::mvar(id),
                rhs: Expr::sort(Level::zero()),
            },
            0,
        );
        let impossible = txn.postpone(
            ConstraintKind::DefEq {
                lhs: Expr::sort(Level::zero()),
                rhs: Expr::sort(Level::one()),
            },
            0,
        );
        let before = txn.clone();
        assert!(
            txn.solve_defeq_constraints_with(&[first, impossible], budget, &|| false)
                .is_err()
        );
        assert_eq!(txn.mvars, before.mvars);
        assert_eq!(txn.universes, before.universes);
        assert_eq!(txn.constraints, before.constraints);
    }

    #[test]
    fn queued_selection_is_order_independent_and_duplicate_safe() {
        let (mut txn, budget, _) = solver_transaction();
        let first = txn.postpone(ground(), 0);
        let second = txn.postpone(ground(), 0);
        let mut other = txn.clone();
        let left = txn
            .solve_defeq_constraints_with(&[second, first, second], budget, &|| false)
            .unwrap();
        let right = other
            .solve_defeq_constraints_with(&[first, second], budget, &|| false)
            .unwrap();
        assert_eq!(left.solved, vec![first, second]);
        assert_eq!(left.solved, right.solved);
        assert_eq!(txn, other);
    }

    #[test]
    fn queued_solver_never_discards_an_unsupported_obligation_kind() {
        let (mut txn, budget, id) = solver_transaction();
        let unsupported = txn.postpone(
            ConstraintKind::SynthInstance {
                class: Expr::sort(Level::zero()),
                mvar: id,
            },
            0,
        );
        let before = txn.clone();
        assert!(matches!(
            txn.solve_defeq_constraints_with(&[unsupported], budget, &|| false),
            Err(ConstraintSolveError::NotDefEq(_))
        ));
        assert_eq!(txn, before);
        assert!(matches!(
            txn.solve_defeq_constraints_with(&[ConstraintId(u64::MAX)], budget, &|| false),
            Err(ConstraintSolveError::Missing(_))
        ));
        assert_eq!(txn, before);
    }
}
