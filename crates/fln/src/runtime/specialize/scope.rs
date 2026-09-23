//! Preflight the work of the core's iterative, capture-avoiding transforms.
//!
//! A substitution visits only nodes whose cached loose-variable range crosses
//! its cutoff, and lifts a replacement only at an occurrence of the replaced
//! variable. Charging the product of both whole syntax trees charged unrelated
//! closed proofs repeatedly and made small dependent programs unexecutable.
//!
//! This envelope follows the same cutoff rules as Expr::{subst,lift}_loose.
//! Every enter/exit is charged before the core runs; replacement lifts are
//! preflighted too. We deliberately count presentations, even for shared DAGs:
//! core memoization can only make the actual work smaller, and fuel never
//! depends on allocation identity or hash-table iteration order.
use super::*;

#[derive(Clone, Copy)]
pub(super) enum Operation<'a> {
    Substitute(&'a Expr),
    Lift(u32),
}

pub(super) fn charge<'a>(
    preparation: &mut Preparation<'_>,
    source: &'a Expr,
    operation: Operation<'a>,
) -> Result<(), IngressError> {
    let mut work = vec![(source, 0u32, operation)];
    while let Some((current, cutoff, operation)) = work.pop() {
        preparation.tick()?;
        // The core returns a clone without walking this subtree. This is a
        // syntactic scope test, never permission to erase runtime computation.
        if current.loose_bvar_range() <= cutoff || matches!(operation, Operation::Lift(0)) {
            continue;
        }
        preparation.tick()?; // reconstruction/exit; memo hits are cheaper
        let mut push = |child, cut, op| -> Result<(), IngressError> {
            reserve(&mut work, preparation.limits.max_nodes)?;
            work.push((child, cut, op));
            Ok(())
        };
        match current.node() {
            ExprNode::BVar { idx } => {
                if let Operation::Substitute(value) = operation
                    && *idx == cutoff
                {
                    // The core lifts this open replacement under precisely
                    // cutoff binders; it does not substitute inside it.
                    push(value, 0, Operation::Lift(cutoff))?;
                }
            }
            ExprNode::App { f, a } => {
                push(a, cutoff, operation)?;
                push(f, cutoff, operation)?;
            }
            ExprNode::Lam {
                binder_type, body, ..
            }
            | ExprNode::ForallE {
                binder_type, body, ..
            } => {
                push(body, cutoff.saturating_add(1), operation)?;
                push(binder_type, cutoff, operation)?;
            }
            ExprNode::LetE {
                type_, value, body, ..
            } => {
                push(body, cutoff.saturating_add(1), operation)?;
                push(value, cutoff, operation)?;
                push(type_, cutoff, operation)?;
            }
            ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => {
                push(expr, cutoff, operation)?;
            }
            ExprNode::FVar { .. }
            | ExprNode::MVar { .. }
            | ExprNode::Sort { .. }
            | ExprNode::Const { .. }
            | ExprNode::Lit { .. } => {}
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests;
