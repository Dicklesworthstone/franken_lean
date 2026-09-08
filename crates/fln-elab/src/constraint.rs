//! Constraint queue and postponed obligations for Athanor (plan §10.1, §10.2).
//!
//! Models defeq constraints, typing obligations, typeclass synthesis goals,
//! and delayed assignments with deterministic, targeted wake-up on assignment.

use crate::mvar::{AssignmentJustification, MetavarError, MetavarStore};
use fln_core::expr::{Expr, FVarId, MVarId};
use std::collections::{BTreeSet, HashMap, HashSet};

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
    DelayedAssign {
        mvar: MVarId,
        fvars: Vec<FVarId>,
        val: Expr,
    },
}

impl ConstraintKind {
    /// Unsolved inputs of this obligation under the current assignment graph.
    /// Synthesis and delayed-assignment targets are outputs, not blockers on
    /// themselves; their declared types and local contexts are inputs.
    pub fn dependencies(&self, store: &MetavarStore) -> HashSet<MVarId> {
        let mut reads = HashSet::new();
        let target = match self {
            Self::DefEq { lhs, rhs } => {
                reads.extend(store.collect_mvars(lhs));
                reads.extend(store.collect_mvars(rhs));
                None
            }
            Self::HasType { expr, expected_type } => {
                reads.extend(store.collect_mvars(expr));
                reads.extend(store.collect_mvars(expected_type));
                None
            }
            Self::SynthInstance { class, mvar } => {
                reads.extend(store.collect_mvars(class));
                Some(mvar)
            }
            Self::DelayedAssign { mvar, val, .. } => {
                reads.extend(store.collect_mvars(val));
                Some(mvar)
            }
        };
        if let Some(decl) = target.and_then(|id| store.get_decl(id)) {
            reads.extend(store.collect_mvars(&decl.type_));
            for local in decl.lctx.decls() {
                reads.extend(store.collect_mvars(&local.type_));
                if let Some(value) = &local.value {
                    reads.extend(store.collect_mvars(value));
                }
            }
        }
        reads
    }
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
/// Hash maps are lookup indexes only: every returned batch is ordered by the
/// monotone constraint identity, independently of hash seeds and input order.
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

    /// Enqueue a constraint with an explicit observed-read signature. Use
    /// `enqueue_inferred` when the obligation's terms are the entire signature.
    pub fn enqueue(
        &mut self,
        kind: ConstraintKind,
        reads_mvars: HashSet<MVarId>,
        depth: u32,
    ) -> ConstraintId {
        let id = ConstraintId(self.next_id);
        self.next_id += 1;
        for mvar in &reads_mvars {
            self.mvar_to_constraints
                .entry(mvar.clone())
                .or_default()
                .insert(id);
        }
        self.constraints.insert(
            id,
            Constraint {
                id,
                kind,
                reads_mvars,
                depth,
            },
        );
        id
    }

    /// Derive the signature after following current assignments, so an alias
    /// that was already assigned does not hide the variable still blocking it.
    pub fn enqueue_inferred(
        &mut self,
        kind: ConstraintKind,
        store: &MetavarStore,
        depth: u32,
    ) -> ConstraintId {
        let reads = kind.dependencies(store);
        self.enqueue(kind, reads, depth)
    }

    /// Update a suspended obligation's observed reads without changing its
    /// identity or scheduling priority. Missing IDs leave the queue unchanged.
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
        self.constraints.insert(id, constraint);
        true
    }

    /// Assign and resume as one operation. The store validates before mutation;
    /// a refusal therefore leaves both the store and this queue untouched.
    /// Resumed obligations are candidates for rechecking, not solved proofs.
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

    /// Extract all constraints that read `mvar`, in stable identity order.
    pub fn wake_up_for_mvar(&mut self, mvar: &MVarId) -> Vec<Constraint> {
        self.wake_up_for_mvars(std::iter::once(mvar))
    }

    /// Extract the union of readers of a changed-variable batch. A constraint
    /// reading multiple affected variables is returned exactly once.
    pub fn wake_up_for_mvars<'a>(
        &mut self,
        mvars: impl IntoIterator<Item = &'a MVarId>,
    ) -> Vec<Constraint> {
        let mut ids = BTreeSet::new();
        for mvar in mvars {
            if let Some(readers) = self.mvar_to_constraints.get(mvar) {
                ids.extend(readers.iter().copied());
            }
        }
        ids.into_iter().filter_map(|id| self.remove(&id)).collect()
    }

    /// Extract obligations with no unresolved inputs, in stable identity order.
    /// This does not decide them: the elaborator must still process each one.
    pub fn take_ready(&mut self) -> Vec<Constraint> {
        let ids: BTreeSet<_> = self
            .constraints
            .values()
            .filter(|constraint| constraint.reads_mvars.is_empty())
            .map(|constraint| constraint.id)
            .collect();
        ids.into_iter().filter_map(|id| self.remove(&id)).collect()
    }

    /// Remove a constraint and every corresponding reverse-index entry.
    pub fn remove(&mut self, id: &ConstraintId) -> Option<Constraint> {
        let constraint = self.constraints.remove(id)?;
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lctx::LocalContext;
    use crate::mvar::MetavarKind;
    use fln_core::level::Level;
    use fln_core::name::Name;
    use fln_core::options::KVMap;

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
        assert_eq!(ready.iter().map(|row| row.id).collect::<Vec<_>>(), vec![first, second, both]);
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
            .assign(a.clone(), Expr::mvar(b.clone()), AssignmentJustification::DirectDefEq)
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
        assert!(queue
            .assign_mvar(
                &mut store,
                a.clone(),
                Expr::mdata(KVMap::new(), Expr::mvar(a)),
                AssignmentJustification::DirectDefEq,
            )
            .is_err());
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
            .assign(a.clone(), Expr::mvar(b.clone()), AssignmentJustification::DirectDefEq)
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
        assert_eq!(queue.constraints()[&id].reads_mvars, HashSet::from([b.clone()]));
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
}
