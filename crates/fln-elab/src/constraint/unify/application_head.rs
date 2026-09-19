//! Recover a function head from an application with an already equal suffix.
//!
//! Miller patterns cannot abstract rigid arguments such as `Nat.succ x` or
//! literals. At the ordinary solver's fixed point, `?f a = g a` may instead
//! choose `?f := g`, including a partially applied `g`. This is an assignment
//! candidate, NOT an injectivity rule: unequal arguments are never equated.
//! The original application is replayed, and the candidate crosses the same
//! scope, occurs, typing, resource and K1 barriers as an ordinary assignment.
use super::*;

impl Engine<'_> {
    pub(super) fn recover_application_head(
        &mut self,
        equation: &Equation,
        pending: &mut VecDeque<Equation>,
    ) -> Result<bool, UnificationError> {
        let (left, right, locals) = equation;
        let left = self.instantiate(left)?;
        let right = self.instantiate(right)?;
        let left = self.whnf(&left, locals)?;
        let right = self.whnf(&right, locals)?;
        if self.align_application_head(&left, &right, locals, pending)? {
            return Ok(true);
        }
        self.align_application_head(&right, &left, locals, pending)
    }

    fn align_application_head(
        &mut self,
        flexible: &Expr,
        other: &Expr,
        locals: &LocalContext,
        pending: &mut VecDeque<Equation>,
    ) -> Result<bool, UnificationError> {
        let mut head = flexible;
        let mut arguments = Vec::new();
        loop {
            self.meter.node()?;
            match head.node() {
                ExprNode::App { f, a } => {
                    arguments.push(a);
                    head = f;
                }
                ExprNode::MData { expr, .. } => head = expr,
                _ => break,
            }
        }
        let ExprNode::MVar { id } = head.node() else {
            return Ok(false);
        };
        let Some(declaration) = self.work.mvars.get_decl(id) else {
            return Ok(false);
        };
        if arguments.is_empty()
            || self.work.mvars.is_assigned(id)
            || declaration.kind == MetavarKind::SyntheticOpaque
            || declaration.depth > self.budget.max_metavar_depth
            || declaration.delayed.is_some()
        {
            return Ok(false);
        }
        let mut candidate = other;
        // Both spines are consumed outside-in, preserving the complete suffix's
        // order and arity. A failed match has made no assignment or queue change.
        for argument in arguments {
            self.meter.node()?;
            while let ExprNode::MData { expr, .. } = candidate.node() {
                self.meter.node()?;
                candidate = expr;
            }
            let ExprNode::App { f, a } = candidate.node() else {
                return Ok(false);
            };
            if !same_terms(argument, a, &mut self.meter)? {
                // Reduction is conversion only, under the caller's existing
                // transparency and local-let policy. It does not solve holes.
                let left = self.whnf(argument, locals)?;
                let right = self.whnf(a, locals)?;
                if !same_terms(&left, &right, &mut self.meter)? {
                    return Ok(false);
                }
            }
            candidate = f;
        }
        let mut rigid = candidate;
        loop {
            self.meter.node()?;
            match rigid.node() {
                ExprNode::App { f, .. } => rigid = f,
                ExprNode::MData { expr, .. } => rigid = expr,
                _ => break,
            }
        }
        if !matches!(rigid.node(), ExprNode::Const { .. } | ExprNode::FVar { .. }) {
            return Ok(false);
        }
        // Submit the WHOLE remaining prefix. Assigning just its root would
        // discard dependent parameters and can change the function's type.
        // `pattern` refuses before mutation; its typing equations must survive
        // alongside the original application and every other postponed row.
        match self.pattern(head, candidate, locals, pending) {
            Err(UnificationError::Deferred(_))
            | Err(UnificationError::Metavariable(MetavarError::OccursCheckFailed { .. })) => {
                Ok(false)
            }
            result => result,
        }
    }
}
