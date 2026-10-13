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
            // Reduction is conversion only, under the caller's existing
            // transparency and local-let policy. It does not solve holes.
            if !same_terms(argument, a, &mut self.meter)?
                && !self.application_suffix_convertible(argument, a, locals)?
            {
                return Ok(false);
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

    /// A sufficient conversion test, never an argument-unification problem.
    /// In particular, no argument hole may be assigned to choose a head.
    /// WHNF alone misses `h (id x) = h x` when `h` is neutral: descend through
    /// congruent applications/projections under the caller's reduction policy.
    fn application_suffix_convertible(
        &mut self,
        left: &Expr,
        right: &Expr,
        locals: &LocalContext,
    ) -> Result<bool, UnificationError> {
        let mut pending = vec![(left.clone(), right.clone())];
        // Own the keyed operands. Reduction allocates temporary expressions;
        // an address-only set could confuse a reused allocation with a proved
        // pair. The retained roots also make shared DAGs safe to memoize.
        let mut seen = HashMap::new();
        while let Some((left, right)) = pending.pop() {
            self.meter.node()?;
            let key = (
                std::ptr::from_ref(left.node()),
                std::ptr::from_ref(right.node()),
            );
            if seen.insert(key, (left.clone(), right.clone())).is_some() {
                continue;
            }
            let left = self.whnf(&left, locals)?;
            let right = self.whnf(&right, locals)?;
            if std::ptr::eq(left.node(), right.node()) {
                continue;
            }
            match (left.node(), right.node()) {
                (ExprNode::BVar { idx: a }, ExprNode::BVar { idx: b }) if a == b => {}
                (ExprNode::FVar { id: a }, ExprNode::FVar { id: b }) if a == b => {}
                (ExprNode::MVar { id: a }, ExprNode::MVar { id: b }) if a == b => {}
                (ExprNode::Lit { literal: a }, ExprNode::Lit { literal: b }) if a == b => {}
                (ExprNode::Sort { level: a }, ExprNode::Sort { level: b }) => {
                    if !same_levels(a, b, &mut self.meter)? {
                        return Ok(false);
                    }
                }
                (
                    ExprNode::Const {
                        name: a,
                        levels: ua,
                    },
                    ExprNode::Const {
                        name: b,
                        levels: ub,
                    },
                ) if a == b && ua.len() == ub.len() => {
                    for (a, b) in ua.iter().zip(ub) {
                        if !same_levels(a, b, &mut self.meter)? {
                            return Ok(false);
                        }
                    }
                }
                (ExprNode::App { f: a, a: b }, ExprNode::App { f: c, a: d }) => {
                    pending.push((b.clone(), d.clone()));
                    pending.push((a.clone(), c.clone()));
                }
                (
                    ExprNode::Proj {
                        struct_name: a,
                        idx: i,
                        expr: x,
                    },
                    ExprNode::Proj {
                        struct_name: b,
                        idx: j,
                        expr: y,
                    },
                ) if a == b && i == j => pending.push((x.clone(), y.clone())),
                // Preserve reflexivity below a reduced binder. Conversion
                // under binders additionally needs a shared, opened context.
                (ExprNode::Lam { .. }, ExprNode::Lam { .. })
                | (ExprNode::ForallE { .. }, ExprNode::ForallE { .. })
                | (ExprNode::LetE { .. }, ExprNode::LetE { .. }) => {
                    if !same_terms(&left, &right, &mut self.meter)? {
                        return Ok(false);
                    }
                }
                _ => return Ok(false),
            }
        }
        Ok(true)
    }
}
