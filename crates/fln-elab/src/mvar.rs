//! Expression metavariable store (`MetavarStore`) and dependency graph for Athanor (plan §10.1).
//!
//! Provides explicit metavariable declarations, kinds (Natural, Synthetic, SyntheticOpaque),
//! delayed assignments, assignment justifications, recursive instantiation, occurs-check,
//! and targeted wake-up dependency tracking.

use std::collections::{HashMap, HashSet};
use fln_core::expr::{Expr, ExprNode, FVarId, MVarId};
use fln_core::name::Name;
use crate::lctx::LocalContext;

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
            Self::AlreadyAssigned { id } => write!(f, "metavariable ?{} is already assigned", id.0.to_display_string()),
            Self::OccursCheckFailed { id } => write!(f, "occurs check failed for metavariable ?{}", id.0.to_display_string()),
            Self::SyntheticOpaqueBlocked { id } => write!(f, "cannot assign synthetic opaque metavariable ?{} via standard unification", id.0.to_display_string()),
            Self::NotDeclared { id } => write!(f, "metavariable ?{} is not declared", id.0.to_display_string()),
        }
    }
}

impl std::error::Error for MetavarError {}

/// Metavariable store managing declarations, assignments, and dependency graph.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct MetavarStore {
    decls: HashMap<MVarId, MetavarDecl>,
    assignments: HashMap<MVarId, MetavarAssignment>,
    /// Maps each mvar to other mvars or entities that depend on it / read it.
    readers: HashMap<MVarId, HashSet<MVarId>>,
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

    /// Declare a new metavariable.
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
        // Collect mvars read by the type and register readership
        let read_mvars = self.collect_mvars(&type_);
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

    /// Check if `id` occurs in `expr` after instantiated assignments.
    pub fn occurs_check(&self, id: &MVarId, expr: &Expr) -> bool {
        let instantiated = self.instantiate(expr);
        let mvars = self.collect_mvars(&instantiated);
        mvars.contains(id)
    }

    /// Assign a metavariable with justification.
    pub fn assign(
        &mut self,
        id: MVarId,
        val: Expr,
        justification: AssignmentJustification,
    ) -> Result<HashSet<MVarId>, MetavarError> {
        let decl = self.decls.get(&id).ok_or_else(|| MetavarError::NotDeclared { id: id.clone() })?;
        if decl.kind == MetavarKind::SyntheticOpaque && justification == AssignmentJustification::DirectDefEq {
            return Err(MetavarError::SyntheticOpaqueBlocked { id });
        }
        if self.assignments.contains_key(&id) {
            return Err(MetavarError::AlreadyAssigned { id });
        }
        if self.occurs_check(&id, &val) {
            return Err(MetavarError::OccursCheckFailed { id });
        }

        // Compute wake-ups: all entities that read `id`
        let wake_ups = self.targeted_wake_up(&id);

        self.assignments.insert(id, MetavarAssignment {
            expr: val,
            justification,
        });

        Ok(wake_ups)
    }

    /// Register a dependency: `reader` reads / depends on `read`.
    pub fn register_reader(&mut self, read: MVarId, reader: MVarId) {
        self.readers.entry(read).or_default().insert(reader);
    }

    /// Targeted wake-up: return the exact set of mvars that read `id`.
    pub fn targeted_wake_up(&self, id: &MVarId) -> HashSet<MVarId> {
        self.readers.get(id).cloned().unwrap_or_default()
    }

    /// Instantiate all assigned metavariables in `expr`.
    pub fn instantiate(&self, expr: &Expr) -> Expr {
        if self.assignments.is_empty() || !expr.data().has_expr_mvar() {
            return expr.clone();
        }
        self.instantiate_inner(expr)
    }

    fn instantiate_inner(&self, expr: &Expr) -> Expr {
        match expr.node() {
            ExprNode::MVar { id } => {
                if let Some(assignment) = self.assignments.get(id) {
                    self.instantiate_inner(&assignment.expr)
                } else {
                    expr.clone()
                }
            }
            ExprNode::App { f, a } => {
                let new_f = self.instantiate_inner(f);
                let new_a = self.instantiate_inner(a);
                if &new_f == f && &new_a == a {
                    expr.clone()
                } else {
                    Expr::app(new_f, new_a)
                }
            }
            ExprNode::Lam {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => {
                let new_type = self.instantiate_inner(binder_type);
                let new_body = self.instantiate_inner(body);
                if &new_type == binder_type && &new_body == body {
                    expr.clone()
                } else {
                    Expr::lam(binder_name.clone(), new_type, new_body, *binder_info)
                }
            }
            ExprNode::ForallE {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => {
                let new_type = self.instantiate_inner(binder_type);
                let new_body = self.instantiate_inner(body);
                if &new_type == binder_type && &new_body == body {
                    expr.clone()
                } else {
                    Expr::forall_e(binder_name.clone(), new_type, new_body, *binder_info)
                }
            }
            ExprNode::LetE {
                decl_name,
                type_,
                value,
                body,
                non_dep,
            } => {
                let new_type = self.instantiate_inner(type_);
                let new_val = self.instantiate_inner(value);
                let new_body = self.instantiate_inner(body);
                if &new_type == type_ && &new_val == value && &new_body == body {
                    expr.clone()
                } else {
                    Expr::let_e(decl_name.clone(), new_type, new_val, new_body, *non_dep)
                }
            }
            ExprNode::Proj {
                struct_name,
                idx,
                expr: inner,
            } => {
                let new_inner = self.instantiate_inner(inner);
                if &new_inner == inner {
                    expr.clone()
                } else {
                    Expr::proj(struct_name.clone(), *idx, new_inner)
                }
            }
            _ => expr.clone(),
        }
    }

    /// Collect all unassigned metavariables appearing in `expr`.
    pub fn collect_mvars(&self, expr: &Expr) -> HashSet<MVarId> {
        let mut mvars = HashSet::new();
        self.collect_mvars_into(expr, &mut mvars);
        mvars
    }

    fn collect_mvars_into(&self, expr: &Expr, mvars: &mut HashSet<MVarId>) {
        if !expr.data().has_expr_mvar() {
            return;
        }
        match expr.node() {
            ExprNode::MVar { id } => {
                if let Some(assignment) = self.assignments.get(id) {
                    self.collect_mvars_into(&assignment.expr, mvars);
                } else {
                    mvars.insert(id.clone());
                }
            }
            ExprNode::App { f, a } => {
                self.collect_mvars_into(f, mvars);
                self.collect_mvars_into(a, mvars);
            }
            ExprNode::Lam {
                binder_type,
                body,
                ..
            }
            | ExprNode::ForallE {
                binder_type,
                body,
                ..
            } => {
                self.collect_mvars_into(binder_type, mvars);
                self.collect_mvars_into(body, mvars);
            }
            ExprNode::LetE {
                type_,
                value,
                body,
                ..
            } => {
                self.collect_mvars_into(type_, mvars);
                self.collect_mvars_into(value, mvars);
                self.collect_mvars_into(body, mvars);
            }
            ExprNode::Proj { expr, .. } => {
                self.collect_mvars_into(expr, mvars);
            }
            _ => {}
        }
    }
}
