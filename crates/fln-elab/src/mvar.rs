//! Expression metavariable store (`MetavarStore`) and dependency graph for Athanor (plan §10.1).
//!
//! Provides explicit metavariable declarations, kinds (Natural, Synthetic, SyntheticOpaque),
//! delayed assignments, assignment justifications, DAG-preserving instantiation, occurs-check,
//! and targeted wake-up dependency tracking.

use crate::lctx::LocalContext;
use fln_core::expr::{Expr, ExprNode, FVarId, MVarId};
use fln_core::name::Name;
use std::collections::{HashMap, HashSet};

/// The kind of metavariable (Lean.MetavarKind).
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum MetavarKind {
    /// Natural metavariable created during elaboration/unification.
    #[default]
    Natural,
    /// Synthetic metavariable to be solved by typeclass resolution or tactics.
    Synthetic,
    /// Synthetic opaque metavariable that must not be solved by ordinary unification.
    SyntheticOpaque,
}

/// A delayed assignment for a higher-order pattern metavariable (Lean.DelayedMetavarAssignment).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DelayedAssignment {
    pub fvars: Vec<FVarId>,
    pub val: Expr,
}

/// Provenance / justification for why a metavariable was assigned.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AssignmentJustification {
    DirectDefEq,
    Tactic { tactic_name: Name },
    InstanceSearch { class_name: Name },
    SyntheticHole,
    Coercion,
    UserGiven,
}

/// An assigned value along with its justification.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MetavarAssignment {
    pub expr: Expr,
    pub justification: AssignmentJustification,
}

/// A declared metavariable with its typing, local context, and kind (Lean.MetavarDecl).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MetavarDecl {
    pub id: MVarId,
    pub user_name: Name,
    pub type_: Expr,
    pub lctx: LocalContext,
    pub kind: MetavarKind,
    pub depth: u32,
    pub origin: Option<Name>,
    pub delayed: Option<DelayedAssignment>,
}

/// Error arising from invalid metavariable operations.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MetavarError {
    AlreadyAssigned { id: MVarId },
    OccursCheckFailed { id: MVarId },
    SyntheticOpaqueBlocked { id: MVarId },
    NotDeclared { id: MVarId },
}

impl std::fmt::Display for MetavarError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::AlreadyAssigned { id } => write!(
                f,
                "metavariable ?{} is already assigned",
                id.0.to_display_string()
            ),
            Self::OccursCheckFailed { id } => write!(
                f,
                "occurs check failed for metavariable ?{}",
                id.0.to_display_string()
            ),
            Self::SyntheticOpaqueBlocked { id } => write!(
                f,
                "cannot assign synthetic opaque metavariable ?{} via standard unification",
                id.0.to_display_string()
            ),
            Self::NotDeclared { id } => write!(
                f,
                "metavariable ?{} is not declared",
                id.0.to_display_string()
            ),
        }
    }
}

impl std::error::Error for MetavarError {}

/// Metavariable store managing declarations, assignments, and dependency graph.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct MetavarStore {
    decls: HashMap<MVarId, MetavarDecl>,
    assignments: HashMap<MVarId, MetavarAssignment>,
    /// Reverse edges from types, local contexts, assignment values and explicit reads.
    readers: HashMap<MVarId, HashSet<MVarId>>,
}

/// Expression children, including metadata. One inventory serves substitution
/// and dependency discovery so a container cannot be transparent to only one.
fn expression_children(expr: &Expr) -> [Option<&Expr>; 3] {
    match expr.node() {
        ExprNode::App { f, a } => [Some(f), Some(a), None],
        ExprNode::Lam {
            binder_type, body, ..
        }
        | ExprNode::ForallE {
            binder_type, body, ..
        } => [Some(binder_type), Some(body), None],
        ExprNode::LetE {
            type_, value, body, ..
        } => [Some(type_), Some(value), Some(body)],
        ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => [Some(expr), None, None],
        ExprNode::BVar { .. }
        | ExprNode::FVar { .. }
        | ExprNode::MVar { .. }
        | ExprNode::Sort { .. }
        | ExprNode::Const { .. }
        | ExprNode::Lit { .. } => [None, None, None],
    }
}

impl MetavarStore {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn is_empty(&self) -> bool {
        self.decls.is_empty()
    }

    pub fn len(&self) -> usize {
        self.decls.len()
    }

    pub fn decls(&self) -> &HashMap<MVarId, MetavarDecl> {
        &self.decls
    }

    pub fn assignments(&self) -> &HashMap<MVarId, MetavarAssignment> {
        &self.assignments
    }

    pub fn get_decl(&self, id: &MVarId) -> Option<&MetavarDecl> {
        self.decls.get(id)
    }

    pub fn is_declared(&self, id: &MVarId) -> bool {
        self.decls.contains_key(id)
    }

    pub fn is_assigned(&self, id: &MVarId) -> bool {
        self.assignments.contains_key(id)
    }

    pub fn get_assignment(&self, id: &MVarId) -> Option<&MetavarAssignment> {
        self.assignments.get(id)
    }

    pub fn get_assigned_expr(&self, id: &MVarId) -> Option<&Expr> {
        self.assignments.get(id).map(|a| &a.expr)
    }

    /// Declare a metavariable and record the unresolved dependencies of its
    /// type and local context, including local let-values hidden by metadata.
    #[allow(clippy::too_many_arguments)]
    pub fn declare(
        &mut self,
        id: MVarId,
        user_name: Name,
        type_: Expr,
        lctx: LocalContext,
        kind: MetavarKind,
        depth: u32,
        origin: Option<Name>,
    ) -> &MetavarDecl {
        let mut read_mvars = self.collect_mvars(&type_);
        for local in lctx.decls() {
            read_mvars.extend(self.collect_mvars(&local.type_));
            if let Some(value) = &local.value {
                read_mvars.extend(self.collect_mvars(value));
            }
        }
        for read in read_mvars {
            self.readers.entry(read).or_default().insert(id.clone());
        }
        self.decls.insert(
            id.clone(),
            MetavarDecl {
                id: id.clone(),
                user_name,
                type_,
                lctx,
                kind,
                depth,
                origin,
                delayed: None,
            },
        );
        self.decls.get(&id).unwrap()
    }

    /// Check if `id` occurs after following assigned metavariables. No expanded
    /// expression is allocated merely to decide whether an assignment is cyclic.
    pub fn occurs_check(&self, id: &MVarId, expr: &Expr) -> bool {
        self.collect_mvars(expr).contains(id)
    }

    /// Assign a metavariable with justification and return all affected readers.
    /// An alias `?a := ?b` records `b -> a`, so assigning `b` later wakes readers
    /// of `a` as well. Validation precedes every mutation of either state map.
    pub fn assign(
        &mut self,
        id: MVarId,
        val: Expr,
        justification: AssignmentJustification,
    ) -> Result<HashSet<MVarId>, MetavarError> {
        let decl = self
            .decls
            .get(&id)
            .ok_or_else(|| MetavarError::NotDeclared { id: id.clone() })?;
        if decl.kind == MetavarKind::SyntheticOpaque
            && justification == AssignmentJustification::DirectDefEq
        {
            return Err(MetavarError::SyntheticOpaqueBlocked { id });
        }
        if self.assignments.contains_key(&id) {
            return Err(MetavarError::AlreadyAssigned { id });
        }
        let dependencies = self.collect_mvars(&val);
        if dependencies.contains(&id) {
            return Err(MetavarError::OccursCheckFailed { id });
        }
        let wake_ups = self.targeted_wake_up(&id);
        for dependency in dependencies {
            self.readers
                .entry(dependency)
                .or_default()
                .insert(id.clone());
        }
        self.assignments.insert(
            id,
            MetavarAssignment {
                expr: val,
                justification,
            },
        );
        Ok(wake_ups)
    }

    /// Register a dependency: `reader` reads / depends on `read`.
    pub fn register_reader(&mut self, read: MVarId, reader: MVarId) {
        self.readers.entry(read).or_default().insert(reader);
    }

    /// Return the transitive reverse-dependency closure, excluding the changed
    /// root itself. Explicit reader cycles terminate; unrelated goals stay asleep.
    /// The set is unordered: consumers must impose their stable scheduling order.
    pub fn targeted_wake_up(&self, id: &MVarId) -> HashSet<MVarId> {
        let mut affected = HashSet::new();
        let mut pending = vec![id];
        while let Some(current) = pending.pop() {
            if let Some(readers) = self.readers.get(current) {
                for reader in readers {
                    if reader != id && affected.insert(reader.clone()) {
                        pending.push(reader);
                    }
                }
            }
        }
        affected
    }

    /// Instantiate assigned metavariables with an explicit postorder worklist.
    /// Every reachable input node is visited once, including through assignment
    /// chains. Rebuilt shared subterms stay shared; unchanged nodes are reused.
    ///
    /// Node addresses are local memo keys only, never ordering or persisted
    /// identity. Input roots and assignments stay borrowed for the whole walk,
    /// so an input allocation cannot disappear and have its address reused.
    #[allow(clippy::too_many_lines)]
    pub fn instantiate(&self, expr: &Expr) -> Expr {
        if self.assignments.is_empty() || !expr.has_expr_mvar() {
            return expr.clone();
        }
        let mut done: HashMap<*const ExprNode, Expr> = HashMap::new();
        let mut pending = vec![(expr, false)];
        while let Some((current, exit)) = pending.pop() {
            let key = std::ptr::from_ref(current.node());
            if done.contains_key(&key) {
                continue;
            }
            if !current.has_expr_mvar() {
                done.insert(key, current.clone());
                continue;
            }
            if !exit {
                pending.push((current, true));
                match current.node() {
                    ExprNode::MVar { id } => {
                        if let Some(assignment) = self.assignments.get(id) {
                            pending.push((&assignment.expr, false));
                        }
                    }
                    _ => {
                        for child in expression_children(current).into_iter().flatten() {
                            pending.push((child, false));
                        }
                    }
                }
                continue;
            }
            let child = |input: &Expr| {
                done.get(&std::ptr::from_ref(input.node()))
                    .expect("postorder substitution finishes each child first")
                    .clone()
            };
            let result = if let ExprNode::MVar { id } = current.node() {
                self.assignments
                    .get(id)
                    .map_or_else(|| current.clone(), |assignment| child(&assignment.expr))
            } else if expression_children(current)
                .into_iter()
                .flatten()
                .all(|input| std::ptr::eq(child(input).node(), input.node()))
            {
                current.clone()
            } else {
                match current.node() {
                    ExprNode::App { f, a } => Expr::app(child(f), child(a)),
                    ExprNode::Lam {
                        binder_name,
                        binder_type,
                        body,
                        binder_info,
                    } => Expr::lam(
                        binder_name.clone(),
                        child(binder_type),
                        child(body),
                        *binder_info,
                    ),
                    ExprNode::ForallE {
                        binder_name,
                        binder_type,
                        body,
                        binder_info,
                    } => Expr::forall_e(
                        binder_name.clone(),
                        child(binder_type),
                        child(body),
                        *binder_info,
                    ),
                    ExprNode::LetE {
                        decl_name,
                        type_,
                        value,
                        body,
                        non_dep,
                    } => Expr::let_e(
                        decl_name.clone(),
                        child(type_),
                        child(value),
                        child(body),
                        *non_dep,
                    ),
                    ExprNode::MData { data, expr } => Expr::mdata(data.clone(), child(expr)),
                    ExprNode::Proj {
                        struct_name,
                        idx,
                        expr,
                    } => Expr::proj(struct_name.clone(), *idx, child(expr)),
                    ExprNode::BVar { .. }
                    | ExprNode::FVar { .. }
                    | ExprNode::MVar { .. }
                    | ExprNode::Sort { .. }
                    | ExprNode::Const { .. }
                    | ExprNode::Lit { .. } => current.clone(),
                }
            };
            done.insert(key, result);
        }
        done.remove(&std::ptr::from_ref(expr.node()))
            .expect("postorder substitution finishes the root")
    }

    /// Collect unassigned metavariables through every expression container and
    /// assignment edge. Shared terms and repeated assignment references are
    /// scanned once, without recursion or expression expansion.
    pub fn collect_mvars(&self, expr: &Expr) -> HashSet<MVarId> {
        let mut mvars = HashSet::new();
        let mut visited = HashSet::new();
        let mut pending = vec![expr];
        while let Some(current) = pending.pop() {
            if !current.has_expr_mvar() || !visited.insert(std::ptr::from_ref(current.node())) {
                continue;
            }
            match current.node() {
                ExprNode::MVar { id } => {
                    if let Some(assignment) = self.assignments.get(id) {
                        pending.push(&assignment.expr);
                    } else {
                        mvars.insert(id.clone());
                    }
                }
                _ => pending.extend(expression_children(current).into_iter().flatten()),
            }
        }
        mvars
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use fln_core::expr::BinderInfo;
    use fln_core::level::Level;
    use fln_core::options::KVMap;

    fn declare(store: &mut MetavarStore, name: &str) -> MVarId {
        let id = MVarId(Name::from_components([name]));
        store.declare(
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

    fn metadata(expr: Expr) -> Expr {
        Expr::mdata(KVMap::new(), expr)
    }

    #[test]
    fn metadata_cannot_hide_a_direct_cycle_and_refusal_is_atomic() {
        let mut store = MetavarStore::new();
        let id = declare(&mut store, "m");
        let before = store.clone();
        assert_eq!(
            store.assign(
                id.clone(),
                metadata(Expr::mvar(id.clone())),
                AssignmentJustification::DirectDefEq,
            ),
            Err(MetavarError::OccursCheckFailed { id }),
        );
        assert_eq!(store, before);
    }

    #[test]
    fn metadata_cannot_hide_a_cycle_through_an_assignment() {
        let mut store = MetavarStore::new();
        let a = declare(&mut store, "a");
        let b = declare(&mut store, "b");
        store
            .assign(
                a.clone(),
                metadata(Expr::mvar(b.clone())),
                AssignmentJustification::DirectDefEq,
            )
            .unwrap();
        let before = store.clone();
        assert_eq!(
            store.assign(
                b.clone(),
                metadata(Expr::mvar(a)),
                AssignmentJustification::DirectDefEq,
            ),
            Err(MetavarError::OccursCheckFailed { id: b }),
        );
        assert_eq!(store, before);
    }

    #[test]
    fn metadata_and_unassigned_dependencies_survive_substitution() {
        let mut store = MetavarStore::new();
        let a = declare(&mut store, "a");
        let b = declare(&mut store, "b");
        store
            .assign(
                a.clone(),
                metadata(Expr::mvar(b.clone())),
                AssignmentJustification::DirectDefEq,
            )
            .unwrap();
        let input = metadata(Expr::mvar(a));
        assert_eq!(store.collect_mvars(&input), HashSet::from([b.clone()]));
        assert_eq!(
            store.instantiate(&input),
            metadata(metadata(Expr::mvar(b.clone()))),
        );
        let value = Expr::sort(Level::zero());
        store
            .assign(b, value.clone(), AssignmentJustification::DirectDefEq)
            .unwrap();
        assert_eq!(store.instantiate(&input), metadata(metadata(value)));
        assert!(store.collect_mvars(&input).is_empty());
    }

    #[test]
    fn every_expression_container_is_substituted() {
        let mut store = MetavarStore::new();
        let id = declare(&mut store, "m");
        let name = Name::from_components(["x"]);
        let build = |term: Expr| {
            Expr::let_e(
                name.clone(),
                term.clone(),
                Expr::lam(
                    name.clone(),
                    term.clone(),
                    Expr::app(term.clone(), Expr::bvar(0).unwrap()),
                    BinderInfo::Implicit,
                ),
                Expr::forall_e(
                    name.clone(),
                    term.clone(),
                    Expr::proj(name.clone(), 2, metadata(term)),
                    BinderInfo::InstImplicit,
                ),
                true,
            )
        };
        let input = build(Expr::mvar(id.clone()));
        assert_eq!(store.collect_mvars(&input), HashSet::from([id.clone()]));
        let value = Expr::sort(Level::zero());
        store
            .assign(id, value.clone(), AssignmentJustification::DirectDefEq)
            .unwrap();
        assert_eq!(store.instantiate(&input), build(value));
    }

    #[test]
    fn an_unaffected_open_subterm_keeps_its_identity() {
        let mut store = MetavarStore::new();
        let assigned = declare(&mut store, "assigned");
        let open = declare(&mut store, "open");
        store
            .assign(
                assigned,
                Expr::sort(Level::zero()),
                AssignmentJustification::DirectDefEq,
            )
            .unwrap();
        let input = metadata(Expr::mvar(open));
        let output = store.instantiate(&input);
        assert!(std::ptr::eq(input.node(), output.node()));
    }

    #[test]
    fn exponentially_shared_input_is_not_expanded_into_a_tree() {
        let mut store = MetavarStore::new();
        let id = declare(&mut store, "m");
        let mut input = Expr::mvar(id.clone());
        for _ in 0..60 {
            input = Expr::app(input.clone(), input);
        }
        assert_eq!(store.collect_mvars(&input), HashSet::from([id.clone()]));
        let value = Expr::sort(Level::zero());
        store
            .assign(id, value.clone(), AssignmentJustification::DirectDefEq)
            .unwrap();
        let mut output = store.instantiate(&input);
        for _ in 0..60 {
            let ExprNode::App { f, a } = output.node() else {
                panic!("shared application shape must be retained");
            };
            assert!(std::ptr::eq(f.node(), a.node()));
            output = f.clone();
        }
        assert_eq!(output, value);
    }

    #[test]
    fn deep_substitution_and_occurs_check_fit_a_small_stack() {
        std::thread::Builder::new()
            .stack_size(64 * 1024)
            .spawn(|| {
                let mut store = MetavarStore::new();
                let id = declare(&mut store, "m");
                let mut input = Expr::mvar(id.clone());
                for _ in 0..20_000 {
                    input = metadata(input);
                }
                assert!(store.occurs_check(&id, &input));
                store
                    .assign(
                        id,
                        Expr::sort(Level::zero()),
                        AssignmentJustification::DirectDefEq,
                    )
                    .unwrap();
                assert!(!store.instantiate(&input).has_expr_mvar());
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn assigning_an_alias_target_wakes_transitive_readers_only() {
        let mut store = MetavarStore::new();
        let a = declare(&mut store, "a");
        let b = declare(&mut store, "b");
        let c = declare(&mut store, "c");
        let unrelated = declare(&mut store, "unrelated");
        let reader = MVarId(Name::from_components(["reader"]));
        store.declare(
            reader.clone(),
            reader.0.clone(),
            metadata(Expr::mvar(a.clone())),
            LocalContext::new(),
            MetavarKind::Natural,
            0,
            None,
        );
        store
            .assign(
                a.clone(),
                metadata(Expr::mvar(b.clone())),
                AssignmentJustification::DirectDefEq,
            )
            .unwrap();
        store
            .assign(
                b.clone(),
                Expr::mvar(c.clone()),
                AssignmentJustification::DirectDefEq,
            )
            .unwrap();
        let affected = store
            .assign(
                c,
                Expr::sort(Level::zero()),
                AssignmentJustification::DirectDefEq,
            )
            .unwrap();
        assert_eq!(affected, HashSet::from([a, b, reader]));
        assert!(!affected.contains(&unrelated));
    }

    #[test]
    fn local_types_and_let_values_participate_in_the_dependency_graph() {
        let mut store = MetavarStore::new();
        let type_dep = declare(&mut store, "type_dep");
        let value_dep = declare(&mut store, "value_dep");
        let mut lctx = LocalContext::new();
        let x = Name::from_components(["x"]);
        lctx.add_param(
            FVarId(x.clone()),
            x,
            metadata(Expr::mvar(type_dep.clone())),
            BinderInfo::Default,
        );
        let y = Name::from_components(["y"]);
        lctx.add_let(
            FVarId(y.clone()),
            y,
            Expr::sort(Level::one()),
            metadata(Expr::mvar(value_dep.clone())),
        );
        let reader = MVarId(Name::from_components(["reader"]));
        store.declare(
            reader.clone(),
            reader.0.clone(),
            Expr::sort(Level::one()),
            lctx,
            MetavarKind::Natural,
            0,
            None,
        );
        assert_eq!(
            store.targeted_wake_up(&type_dep),
            HashSet::from([reader.clone()])
        );
        assert_eq!(store.targeted_wake_up(&value_dep), HashSet::from([reader]));
    }

    #[test]
    fn explicit_reader_cycles_terminate_without_waking_the_root() {
        let mut store = MetavarStore::new();
        let a = declare(&mut store, "a");
        let b = declare(&mut store, "b");
        store.register_reader(a.clone(), a.clone());
        store.register_reader(a.clone(), b.clone());
        store.register_reader(b.clone(), a.clone());
        assert_eq!(store.targeted_wake_up(&a), HashSet::from([b]));
    }

    #[test]
    fn child_assignment_dependencies_do_not_leak_into_a_snapshot() {
        let mut parent = MetavarStore::new();
        let a = declare(&mut parent, "a");
        let b = declare(&mut parent, "b");
        let mut child = parent.clone();
        child
            .assign(
                a.clone(),
                Expr::mvar(b.clone()),
                AssignmentJustification::DirectDefEq,
            )
            .unwrap();
        assert_eq!(child.targeted_wake_up(&b), HashSet::from([a.clone()]));
        assert!(parent.targeted_wake_up(&b).is_empty());
        assert!(!parent.is_assigned(&a));
    }
}
