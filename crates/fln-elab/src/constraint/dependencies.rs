//! Input dependencies include types and retained lexical environments, not only
//! metavariables syntactically present in the displayed constraint. One heap
//! walk follows assignments and declared-type edges; even cyclic untrusted
//! metadata terminates. This computes a scheduling signature, not a verdict.
use super::ConstraintKind;
use crate::lctx::LocalContext;
use crate::mvar::MetavarStore;
use fln_core::expr::{Expr, ExprNode, MVarId};
use std::collections::HashSet;

pub(super) fn reads(
    kind: &ConstraintKind,
    store: &MetavarStore,
    locals: Option<&LocalContext>,
    observed: &HashSet<MVarId>,
) -> HashSet<MVarId> {
    let observed_terms: Vec<_> = observed.iter().cloned().map(Expr::mvar).collect();
    let mut pending: Vec<&Expr> = observed_terms.iter().collect();
    let target = match kind {
        ConstraintKind::DefEq { lhs, rhs } => {
            pending.extend([lhs, rhs]);
            None
        }
        ConstraintKind::HasType {
            expr,
            expected_type,
        } => {
            pending.extend([expr, expected_type]);
            None
        }
        ConstraintKind::SynthInstance { class, mvar } => {
            pending.push(class);
            Some(mvar)
        }
        ConstraintKind::DelayedAssign { mvar, val, .. } => {
            pending.push(val);
            Some(mvar)
        }
    };
    if let Some(locals) = locals {
        // The conditional K1 closure validates the entire saved telescope,
        // including local let annotations and values, not just visible fvars.
        for local in locals.decls() {
            pending.push(&local.type_);
            pending.extend(local.value.as_ref());
        }
    }
    if let Some(target) = target {
        if let Some(decl) = store.get_decl(target) {
            pending.push(&decl.type_);
            for local in decl.lctx.decls() {
                pending.push(&local.type_);
                pending.extend(local.value.as_ref());
            }
        }
        // A preassigned delayed output is checked, never overwritten. Its
        // residual inputs can therefore wake the obligation too.
        pending.extend(store.get_assigned_expr(target));
    }
    let mut result = HashSet::new();
    let mut syntax = HashSet::new();
    let mut declarations = HashSet::new();
    while let Some(expr) = pending.pop() {
        if !syntax.insert(expr.allocation_identity()) {
            continue;
        }
        match expr.node() {
            ExprNode::MVar { id } => {
                if let Some(value) = store.get_assigned_expr(id) {
                    pending.push(value);
                } else {
                    result.insert(id.clone());
                }
                if declarations.insert(id.clone())
                    && let Some(decl) = store.get_decl(id)
                {
                    pending.push(&decl.type_);
                    for local in decl.lctx.decls() {
                        pending.push(&local.type_);
                        pending.extend(local.value.as_ref());
                    }
                }
            }
            ExprNode::App { f, a } => pending.extend([f, a]),
            ExprNode::Lam {
                binder_type, body, ..
            }
            | ExprNode::ForallE {
                binder_type, body, ..
            } => pending.extend([binder_type, body]),
            ExprNode::LetE {
                type_, value, body, ..
            } => pending.extend([type_, value, body]),
            ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => pending.push(expr),
            _ => {}
        }
    }
    result
}
