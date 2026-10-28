//! Recover a function head from an application with an already equal suffix.
//!
//! Miller patterns cannot abstract rigid arguments such as `Nat.succ x` or
//! literals. At the ordinary solver's fixed point, `?f a = g a` may instead
//! choose `?f := g`, including a partially applied `g`. This is an assignment
//! candidate, NOT an injectivity rule: unequal arguments are never equated.
//! The original application is replayed, and the candidate crosses the same
//! scope, occurs, typing, resource and K1 barriers as an ordinary assignment.
//!
//! The pin's own first-order approximation, `processAssignmentFOApprox`, is
//! [`Engine::first_order_approximation`]: it runs for an application whose arguments are not
//! distinct locals outside the hole's own context, at once for a local of that context and at
//! the batch's fixed point otherwise, and it unifies arguments.
use super::application_congruence::{CongruenceResult, MAX_CONGRUENCE_DEPTH};
use super::*;

struct SuffixEta {
    domains: (Expr, Expr),
    bodies: (Expr, Expr),
    locals: LocalContext,
}

impl Engine<'_> {
    pub(super) fn recover_application_head(
        &mut self,
        equation: &Equation,
        pending: &mut VecDeque<Equation>,
    ) -> Result<bool, UnificationError> {
        let (left, right, locals) = equation;
        let left = self.instantiate(left)?;
        let right = self.instantiate(right)?;
        self.meter.node()?;
        // Head recovery can assign only an expression metavariable. Do not
        // recompute a closed failed equation looking for an impossible hole.
        // Free locals retain the old path when zeta may reveal a hidden one.
        if [&left, &right]
            .iter()
            .all(|expr| !expr.has_expr_mvar() && (!self.budget.zeta_delta || !expr.has_fvar()))
        {
            return Ok(false);
        }
        let left = self.whnf(&left, locals)?;
        let right = self.whnf(&right, locals)?;
        if self.align_application_head(&left, &right, locals, pending)? {
            return Ok(true);
        }
        self.align_application_head(&right, &left, locals, pending)
    }

    /// The pin's `processAssignmentFOApprox` (vendored `Lean/Meta/ExprDefEq.lean:1172-1212`)
    /// for `?m a₁ … aₙ =?= v`: head-beta `v`; when it is an application `f a`, unify `aₙ`
    /// with `a` and then `?m a₁ … aₙ₋₁` with `f`, as one trial that commits only a complete
    /// solution (`checkpointDefEq`); otherwise, or when that trial fails, unfold `v`'s head
    /// definition once (`unfoldDefinition?`, `Lean/Meta/WHNF.lean:871`) and try again. `v`
    /// is not reduced first, so `?m σ =?= StateT σ Id σ` gives `?m := StateT σ Id`, and the
    /// arguments are unified, not merely compared as [`Self::recover_application_head`]
    /// compares them. A failed attempt makes no assignment, though its work stays spent.
    pub(super) fn first_order_approximation(
        &mut self,
        flexible: &Expr,
        value: &Expr,
        locals: &LocalContext,
    ) -> Result<bool, UnificationError> {
        // Each attempt nests a trial, and its function equation may approximate again.
        if self.congruence_depth >= MAX_CONGRUENCE_DEPTH {
            return Ok(false);
        }
        let mut flexible = flexible;
        while let ExprNode::MData { expr, .. } = flexible.node() {
            self.meter.node()?;
            flexible = expr;
        }
        let ExprNode::App {
            f: function,
            a: last,
        } = flexible.node()
        else {
            return Ok(false);
        };
        let mut value = self.instantiate(value)?;
        loop {
            self.meter.tick()?;
            value = self.first_order_head_beta(value)?;
            let mut candidate = &value;
            while let ExprNode::MData { expr, .. } = candidate.node() {
                self.meter.node()?;
                candidate = expr;
            }
            if let ExprNode::App { f, a } = candidate.node() {
                let equations = [
                    (last.clone(), a.clone(), locals.clone()),
                    (function.clone(), f.clone(), locals.clone()),
                ];
                let outer = std::mem::replace(&mut self.first_order_trial, true);
                let trial = self.try_congruence_equations(&equations, true);
                self.first_order_trial = outer;
                if matches!(trial?, CongruenceResult::Solved) {
                    return Ok(true);
                }
            }
            match self.unfold_definition_step(&value, locals)? {
                Some(unfolded) => value = unfolded,
                None => return Ok(false),
            }
        }
    }

    /// `Expr.headBeta`: `(fun x => b) a …` reduced at its head until it is no such redex.
    fn first_order_head_beta(&mut self, mut expr: Expr) -> Result<Expr, UnificationError> {
        loop {
            let mut head = &expr;
            let mut arguments = Vec::new();
            while let ExprNode::App { f, a } = head.node() {
                self.meter.node()?;
                arguments.push(a.clone());
                head = f;
            }
            let ExprNode::Lam { body, .. } = head.node() else {
                return Ok(expr);
            };
            let Some(argument) = arguments.pop() else {
                return Ok(expr);
            };
            let reduced = self.substitute(body, &argument)?;
            expr = arguments.into_iter().rev().fold(reduced, Expr::app);
        }
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
    /// congruent applications, projections and binders under that policy.
    fn application_suffix_convertible(
        &mut self,
        left: &Expr,
        right: &Expr,
        locals: &LocalContext,
    ) -> Result<bool, UnificationError> {
        for _ in locals.decls() {
            self.meter.node()?;
        }
        let mut contexts = vec![locals.clone()];
        let mut pending = vec![(left.clone(), right.clone(), 0_usize)];
        // Own the keyed operands. Reduction allocates temporary expressions;
        // an address-only set could confuse a reused allocation with a visited
        // pair. The retained roots also make shared DAGs safe to memoize.
        let mut seen = HashMap::new();
        while let Some((left, right, scope)) = pending.pop() {
            self.meter.node()?;
            let key = (
                std::ptr::from_ref(left.node()),
                std::ptr::from_ref(right.node()),
                scope,
            );
            if seen.insert(key, (left.clone(), right.clone())).is_some() {
                continue;
            }
            let locals = &contexts[scope];
            let left = self.whnf(&left, locals)?;
            let right = self.whnf(&right, locals)?;
            if std::ptr::eq(left.node(), right.node()) {
                continue;
            }
            if self.budget.proof_irrelevance {
                let mut obligations = VecDeque::new();
                match self.proof_irrelevance(&left, &right, locals, &mut obligations) {
                    Ok(true) => {
                        // K1 validates BOTH original proofs, but may unfold more
                        // than this caller allows. Retain every type equation
                        // and compare it here without assigning argument holes.
                        for (a, b, context) in obligations {
                            self.meter.node()?;
                            let type_scope = contexts.len();
                            contexts.push(context);
                            pending.push((a, b, type_scope));
                        }
                        continue;
                    }
                    Ok(false) => {}
                    Err(UnificationError::Deferred(_)) => return Ok(false),
                    Err(error) => return Err(error),
                }
            }
            if let Some(eta) = self.application_suffix_eta(&left, &right, locals)? {
                let body_scope = contexts.len();
                contexts.push(eta.locals);
                pending.push((eta.bodies.0, eta.bodies.1, body_scope));
                // Check the neutral function's domain too. Merely applying it
                // to a fresh local can hide an ill-typed eta expansion.
                pending.push((eta.domains.0, eta.domains.1, scope));
                continue;
            }
            if let Some(eta) = self.record_eta_equations(&left, &right, locals)? {
                // Only decompose here: the ordinary record_eta entry also
                // solves fields and inverts singleton projections. Doing that
                // in this suffix check could choose a head by solving its
                // arguments. Keep the full type equation, even for empty
                // records, followed by every field in declaration order.
                // All these equations retain this exact context. Reuse its
                // scope key so shared fields stay shared in the memo table.
                for (a, b, _) in eta.children.into_iter().rev() {
                    self.meter.node()?;
                    pending.push((a, b, scope));
                }
                continue;
            }
            match (left.node(), right.node()) {
                (ExprNode::BVar { idx: a }, ExprNode::BVar { idx: b }) if a == b => {}
                (ExprNode::FVar { id: a }, ExprNode::FVar { id: b }) if a == b => {}
                (ExprNode::MVar { id: a }, ExprNode::MVar { id: b }) if a == b => {}
                (ExprNode::Lit { literal: a }, ExprNode::Lit { literal: b }) if a == b => {}
                (ExprNode::Sort { level: a }, ExprNode::Sort { level: b }) => {
                    if !self.application_suffix_levels_equal(a, b)? {
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
                        if !self.application_suffix_levels_equal(a, b)? {
                            return Ok(false);
                        }
                    }
                }
                (ExprNode::App { f: a, a: b }, ExprNode::App { f: c, a: d }) => {
                    pending.push((b.clone(), d.clone(), scope));
                    pending.push((a.clone(), c.clone(), scope));
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
                ) if a == b && i == j => pending.push((x.clone(), y.clone(), scope)),
                (
                    ExprNode::Lam {
                        binder_type: a,
                        body: b,
                        binder_info,
                        ..
                    },
                    ExprNode::Lam {
                        binder_type: c,
                        body: d,
                        ..
                    },
                )
                | (
                    ExprNode::ForallE {
                        binder_type: a,
                        body: b,
                        binder_info,
                        ..
                    },
                    ExprNode::ForallE {
                        binder_type: c,
                        body: d,
                        ..
                    },
                ) => {
                    // Open BOTH bodies with one fresh local, not by comparing
                    // raw de Bruijn indices at different depths. Compare the
                    // domains too, even when neither body uses its parameter.
                    let id = self.fresh()?;
                    let argument = Expr::fvar(id.clone());
                    let left_body = self.substitute(b, &argument)?;
                    let right_body = self.substitute(d, &argument)?;
                    for _ in locals.decls() {
                        self.meter.node()?;
                    }
                    let mut inner = locals.clone();
                    inner.add_param(id.clone(), id.0, a.clone(), *binder_info);
                    let body_scope = contexts.len();
                    contexts.push(inner);
                    pending.push((left_body, right_body, body_scope));
                    pending.push((a.clone(), c.clone(), scope));
                }
                (ExprNode::LetE { .. }, ExprNode::LetE { .. }) => {
                    if !same_terms(&left, &right, &mut self.meter)? {
                        return Ok(false);
                    }
                }
                _ => return Ok(false),
            }
        }
        Ok(true)
    }

    /// Open one lambda against a neutral function, using its actual domain as
    /// an additional conversion obligation. No function hole is solved here.
    fn application_suffix_eta(
        &mut self,
        left: &Expr,
        right: &Expr,
        locals: &LocalContext,
    ) -> Result<Option<SuffixEta>, UnificationError> {
        let (lambda, other, reverse) = match (left.node(), right.node()) {
            // Paired lambdas use the ordinary binder rule below.
            (ExprNode::Lam { .. }, ExprNode::Lam { .. }) => return Ok(None),
            (ExprNode::Lam { .. }, _) => (left, right, false),
            (_, ExprNode::Lam { .. }) => (right, left, true),
            _ => return Ok(None),
        };
        let ExprNode::Lam {
            binder_type,
            body,
            binder_info,
            ..
        } = lambda.node()
        else {
            unreachable!("selected lambda");
        };
        let Some(other_type) = self.eta_neutral_type(other, locals)? else {
            return Ok(None);
        };
        let ExprNode::ForallE {
            binder_type: other_domain,
            ..
        } = other_type.node()
        else {
            return Ok(None);
        };
        let id = self.fresh()?;
        let argument = Expr::fvar(id.clone());
        let body = self.substitute(body, &argument)?;
        let applied = Expr::app(other.clone(), argument);
        self.scan(&applied)?;
        for _ in locals.decls() {
            self.meter.node()?;
        }
        let mut inner = locals.clone();
        inner.add_param(id.clone(), id.0, binder_type.clone(), *binder_info);
        let (domains, bodies) = if reverse {
            ((other_domain.clone(), binder_type.clone()), (applied, body))
        } else {
            ((binder_type.clone(), other_domain.clone()), (body, applied))
        };
        Ok(Some(SuffixEta {
            domains,
            bodies,
            locals: inner,
        }))
    }

    /// Normalize identities only. In particular, `max ?u 0 = ?u` may succeed
    /// without choosing ?u, whereas two distinct universe holes stay distinct.
    fn application_suffix_levels_equal(
        &mut self,
        left: &Level,
        right: &Level,
    ) -> Result<bool, UnificationError> {
        if same_levels(left, right, &mut self.meter)? {
            return Ok(true);
        }
        let left = simplify_level(left, &mut self.meter)?;
        let right = simplify_level(right, &mut self.meter)?;
        same_levels(&left, &right, &mut self.meter)
    }
}
