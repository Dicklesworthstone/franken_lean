//! Local context (`LocalContext`) and local declaration (`LocalDecl`) models
//! for Athanor (plan §10.1).
//!
//! Tracks free variables, binder names, types, optional let-values, binder info,
//! and declaration order.

use fln_core::expr::{BinderInfo, Expr, FVarId};
use fln_core::name::Name;

/// A local declaration in a local context (Lean.LocalDecl).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LocalDecl {
    pub id: FVarId,
    pub user_name: Name,
    pub type_: Expr,
    pub value: Option<Expr>,
    pub binder_info: BinderInfo,
    pub index: usize,
}

impl LocalDecl {
    pub fn is_let(&self) -> bool {
        self.value.is_some()
    }

    pub fn is_param(&self) -> bool {
        self.value.is_none()
    }
}

/// A local context representing in-scope free variables (Lean.LocalContext).
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct LocalContext {
    decls: Vec<LocalDecl>,
}

impl LocalContext {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn is_empty(&self) -> bool {
        self.decls.is_empty()
    }

    pub fn len(&self) -> usize {
        self.decls.len()
    }

    pub fn decls(&self) -> &[LocalDecl] {
        &self.decls
    }

    pub fn find(&self, fvar: &FVarId) -> Option<&LocalDecl> {
        self.decls.iter().find(|decl| &decl.id == fvar)
    }

    pub fn find_by_user_name(&self, name: &Name) -> Option<&LocalDecl> {
        self.decls.iter().rev().find(|decl| &decl.user_name == name)
    }

    pub fn contains(&self, fvar: &FVarId) -> bool {
        self.find(fvar).is_some()
    }

    /// Add a parameter declaration (non-let binder).
    pub fn add_param(&mut self, id: FVarId, user_name: Name, type_: Expr, binder_info: BinderInfo) -> &LocalDecl {
        let index = self.decls.len();
        self.decls.push(LocalDecl {
            id,
            user_name,
            type_,
            value: None,
            binder_info,
            index,
        });
        self.decls.last().unwrap()
    }

    /// Add a let-bound local declaration.
    pub fn add_let(&mut self, id: FVarId, user_name: Name, type_: Expr, value: Expr) -> &LocalDecl {
        let index = self.decls.len();
        self.decls.push(LocalDecl {
            id,
            user_name,
            type_,
            value: Some(value),
            binder_info: BinderInfo::Default,
            index,
        });
        self.decls.last().unwrap()
    }

    /// Pop declarations added past `checkpoint` length.
    pub fn truncate(&mut self, checkpoint: usize) {
        self.decls.truncate(checkpoint);
    }
}
