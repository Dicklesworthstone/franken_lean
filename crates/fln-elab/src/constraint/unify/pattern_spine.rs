//! Expose reducible higher-order pattern arguments without assuming injectivity.
//!
//! Weak-head reduction stops at an unknown function. Its arguments may still
//! be beta/zeta/delta/iota redexes denoting distinct locals. Normalize those
//! arguments before retrying pattern recognition and reflexivity, so replaying an
//! equation after an assignment does not get stuck on the original redexes.
//! This is conversion only: it never assigns a hole or decomposes a flexible
//! equation into argument equations. Scope, occurs, depth and K1 checks remain
//! the responsibility of the ordinary assignment and pruning paths.
use super::*;

impl Engine<'_> {
    pub(super) fn pattern_whnf(
        &mut self,
        expr: &Expr,
        locals: &LocalContext,
    ) -> Result<Expr, UnificationError> {
        let reduced = self.whnf(expr, locals)?;
        let mut head = &reduced;
        let mut arguments = Vec::new();
        loop {
            self.meter.node()?;
            match head.node() {
                ExprNode::App { f, a } => {
                    arguments.push((head, f, a));
                    head = f;
                }
                ExprNode::MData { expr, .. } => head = expr,
                _ => break,
            }
        }
        if arguments.is_empty()
            || !matches!(head.node(), ExprNode::MVar { id } if !self.work.mvars.is_assigned(id))
        {
            return Ok(reduced);
        }
        let mut result = head.clone();
        // Restore source order. Every reduction uses the caller's transparency,
        // zeta-delta policy, cancellation callback and shared work budget.
        for (original, function, argument) in arguments.into_iter().rev() {
            let value = self.whnf(argument, locals)?;
            self.meter.node()?;
            result = if std::ptr::eq(function.node(), result.node())
                && std::ptr::eq(argument.node(), value.node())
            {
                // Preserve unchanged spines and their DAG sharing/cache keys.
                original.clone()
            } else {
                Expr::app(result, value)
            };
        }
        self.scan(&result)?;
        Ok(result)
    }
}
