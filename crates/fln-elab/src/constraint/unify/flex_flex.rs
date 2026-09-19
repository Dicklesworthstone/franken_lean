//! Dependency-pruned higher-order patterns, attempted only at a fixed point.
//!
//! `?f x y = ?f x z` can retain the common first argument without choosing a
//! value for the result: `?f := fun x _ => ?h x`. The fresh `?h` is an ordinary
//! declared, typed residual, never an assumed proof. K1 checks every assignment
//! through the parent's existing barrier. The original equation is replayed.
//!
//! The bounded fragment uses distinct local arguments outside the captured
//! metavariable context. Dropping an argument that a retained domain or result
//! depends on is refused. Captured-argument, nonpattern and opaque cases keep
//! their existing postponement behavior; this is not full Lean unification.
//!
//! Distinct heads share the intersection of their local arguments, even when
//! the argument orders or arities differ. The residual captures only their
//! common lexical context, never the union of private locals. Its depth is no
//! deeper than either parent. Both reconstructed assignments cross K1.
//! Bare holes participate too: after scope-aware ordinary orientation fails,
//! sibling holes can depend on one residual restricted to their common parent.
//! A bare/applied pair uses that same construction with an empty telescope on
//! the bare side. The shared residual remains an obligation, including in Prop.
use super::*;
use crate::constraint::ConstraintKind;
use crate::mvar::MetavarDecl;
use fln_core::expr::BinderInfo;

type PatternBinder = (FVarId, Expr, BinderInfo);

struct PruningPattern {
    declaration: MetavarDecl,
    binders: Vec<PatternBinder>,
    result_type: Expr,
}

impl Engine<'_> {
    /// Last-resort progress, after ordinary equations have exhausted their
    /// assignment generation. Never remove the original equation here: replay
    /// it through `compare`, then validate the assignments through K1.
    pub(super) fn prune_flex_flex(
        &mut self,
        equation: &Equation,
    ) -> Result<bool, UnificationError> {
        let (left, right, locals) = equation;
        let Some(left) = self.pruning_pattern(left, locals)? else {
            return Ok(false);
        };
        let Some(right) = self.pruning_pattern(right, locals)? else {
            return Ok(false);
        };
        let same_head = left.declaration.id == right.declaration.id;
        if same_head && left.binders.len() != right.binders.len() {
            return Ok(false);
        }
        // A hole created before an intro and one created after it may still
        // share a solution. Keep only the exact common lexical prefix; using
        // either entire context would let a private local escape into the other
        // assignment. Sibling scopes similarly retain just their common parent.
        let mut common = LocalContext::new();
        for (a, b) in left
            .declaration
            .lctx
            .decls()
            .iter()
            .zip(right.declaration.lctx.decls())
        {
            self.meter.node()?;
            if a != b {
                break;
            }
            if let Some(value) = &a.value {
                common.add_let(
                    a.id.clone(),
                    a.user_name.clone(),
                    a.type_.clone(),
                    value.clone(),
                );
            } else {
                common.add_param(
                    a.id.clone(),
                    a.user_name.clone(),
                    a.type_.clone(),
                    a.binder_info,
                );
            }
        }
        let mut retained = Vec::new();
        if same_head {
            for (index, (a, b)) in left.binders.iter().zip(&right.binders).enumerate() {
                self.meter.node()?;
                if a.0 == b.0 {
                    retained.push(index);
                }
            }
        } else {
            let mut right_arguments = HashSet::new();
            for (id, _, _) in &right.binders {
                self.meter.node()?;
                right_arguments.insert(id.clone());
            }
            // Hash iteration never determines the residual telescope's order.
            for (index, (id, _, _)) in left.binders.iter().enumerate() {
                self.meter.node()?;
                if right_arguments.contains(id) {
                    retained.push(index);
                }
            }
        }
        if (same_head && retained.len() == left.binders.len())
            || !same_terms(&left.result_type, &right.result_type, &mut self.meter)?
        {
            return Ok(false);
        }
        let mut residual_type = left.result_type.clone();
        for &index in retained.iter().rev() {
            let (id, domain, style) = &left.binders[index];
            self.scan(&residual_type)?;
            residual_type = residual_type
                .abstract_fvar(id, 0)
                .map_err(|_| UnificationError::ExpressionScope)?;
            residual_type = Expr::forall_e(id.0.clone(), domain.clone(), residual_type, *style);
        }
        // This also checks retained binder domains. In the dependent fragment,
        // intersection is legal only when its entire telescope is well-scoped.
        let free = self.scan(&residual_type)?.fvars;
        if residual_type.has_loose_bvars() || free.iter().any(|id| !common.contains(id)) {
            return Ok(false);
        }
        let assignments = if same_head { 1 } else { 2 };
        if self.generation().saturating_add(assignments) > self.budget.max_assignments {
            return Err(UnificationError::AssignmentLimit {
                limit: self.budget.max_assignments,
            });
        }
        let residual = self.fresh_pruning_metavariable()?;
        let mut body = Expr::mvar(residual.clone());
        for &index in &retained {
            self.meter.node()?;
            body = Expr::app(body, Expr::fvar(left.binders[index].0.clone()));
        }
        let value = self.close_pruning_lambda(body.clone(), &left.binders)?;
        let other = self.close_pruning_lambda(body, &right.binders)?;
        if same_head && !same_terms(&value, &other, &mut self.meter)? {
            return Ok(false);
        }
        self.meter.node()?;
        self.work.mvars.declare(
            residual.clone(),
            residual.0.clone(),
            residual_type,
            common,
            MetavarKind::Natural,
            // Each parent's conditional K1 check must be allowed to quantify
            // this residual. A shallower parent cannot depend on a deeper hole.
            left.declaration.depth.min(right.declaration.depth),
            Some(left.declaration.id.0.clone()),
        );
        let id = left.declaration.id;
        let awakened = self
            .work
            .assign_mvar(id.clone(), value, AssignmentJustification::DirectDefEq)
            .map_err(UnificationError::Metavariable)?;
        self.awakened.extend(awakened);
        self.assigned.push(id);
        if !same_head {
            let id = right.declaration.id;
            let awakened = self
                .work
                .assign_mvar(id.clone(), other, AssignmentJustification::DirectDefEq)
                .map_err(UnificationError::Metavariable)?;
            self.awakened.extend(awakened);
            self.assigned.push(id);
        }
        Ok(true)
    }

    fn pruning_pattern(
        &mut self,
        expr: &Expr,
        locals: &LocalContext,
    ) -> Result<Option<PruningPattern>, UnificationError> {
        let normalized = self.pattern_whnf(expr, locals)?;
        let mut head = &normalized;
        let mut arguments = Vec::new();
        loop {
            self.meter.node()?;
            match head.node() {
                ExprNode::App { f, a } => {
                    arguments.push(a.clone());
                    head = f;
                }
                ExprNode::MData { expr, .. } => head = expr,
                _ => break,
            }
        }
        let ExprNode::MVar { id } = head.node() else {
            return Ok(None);
        };
        let Some(declaration) = self.work.mvars.get_decl(id).cloned() else {
            return Ok(None);
        };
        if self.work.mvars.is_assigned(id)
            || declaration.kind == MetavarKind::SyntheticOpaque
            || declaration.depth > self.budget.max_metavar_depth
            || declaration.delayed.is_some()
        {
            return Ok(None);
        }
        arguments.reverse();
        let mut binders = Vec::new();
        let mut distinct = HashSet::new();
        let mut type_ = declaration.type_.clone();
        for argument in arguments {
            self.meter.node()?;
            let ExprNode::FVar { id } = argument.node() else {
                return Ok(None);
            };
            // A local captured by the hole is not a Miller-pattern parameter.
            // Keep those equations for ordinary assignment/reduction instead.
            let Some(local) = locals.find(id) else {
                return Ok(None);
            };
            if local.is_let() || declaration.lctx.contains(id) || !distinct.insert(id.clone()) {
                return Ok(None);
            }
            type_ = self.whnf(&type_, locals)?;
            let ExprNode::ForallE {
                binder_type,
                binder_info,
                body,
                ..
            } = type_.node()
            else {
                return Ok(None);
            };
            binders.push((id.clone(), binder_type.clone(), *binder_info));
            type_ = self.substitute(body, &argument)?;
        }
        let result_type = self.whnf(&type_, locals)?;
        Ok(Some(PruningPattern {
            declaration,
            binders,
            result_type,
        }))
    }

    fn close_pruning_lambda(
        &mut self,
        mut body: Expr,
        binders: &[PatternBinder],
    ) -> Result<Expr, UnificationError> {
        for (id, domain, style) in binders.iter().rev() {
            self.scan(&body)?;
            body = body
                .abstract_fvar(id, 0)
                .map_err(|_| UnificationError::ExpressionScope)?;
            body = Expr::lam(id.0.clone(), domain.clone(), body, *style);
        }
        self.scan(&body)?;
        Ok(body)
    }

    /// Reserve every known AND unknown identity in active terms/obligations.
    /// Checking only declared IDs would silently declare an unrelated dangling
    /// input hole when its name happened to match our deterministic namespace.
    fn fresh_pruning_metavariable(&mut self) -> Result<MVarId, UnificationError> {
        let mut reserved = HashSet::new();
        let mut roots = Vec::new();
        for (id, declaration) in self.work.mvars.decls() {
            self.meter.node()?;
            reserved.insert(id.clone());
            if let Some(delayed) = &declaration.delayed {
                roots.push(delayed.val.clone());
            }
        }
        // `solve` scans all input equations, metavariable types/assignments and
        // local types/values before reaching this rung. The cache pins the roots.
        for (expr, _) in self.fact_cache.values() {
            self.meter.node()?;
            roots.push(expr.clone());
        }
        for constraint in self
            .work
            .constraints
            .constraints()
            .values()
            .chain(self.awakened.iter())
        {
            self.meter.node()?;
            for id in &constraint.reads_mvars {
                self.meter.node()?;
                reserved.insert(id.clone());
            }
            match &constraint.kind {
                ConstraintKind::DefEq { lhs, rhs } => {
                    roots.push(lhs.clone());
                    roots.push(rhs.clone());
                }
                ConstraintKind::HasType {
                    expr,
                    expected_type,
                } => {
                    roots.push(expr.clone());
                    roots.push(expected_type.clone());
                }
                ConstraintKind::SynthInstance { class, mvar } => {
                    reserved.insert(mvar.clone());
                    roots.push(class.clone());
                }
                ConstraintKind::DelayedAssign { mvar, val, .. } => {
                    reserved.insert(mvar.clone());
                    roots.push(val.clone());
                }
            }
        }
        let mut seen = HashSet::new();
        // Keep all source allocations pinned until the identity walk ends.
        let mut pending: Vec<_> = roots.iter().collect();
        while let Some(expr) = pending.pop() {
            self.meter.tick()?;
            if !seen.insert(expr.allocation_identity()) {
                continue;
            }
            self.meter.node()?;
            if let ExprNode::MVar { id } = expr.node() {
                reserved.insert(id.clone());
            }
            pending.extend(children(expr).into_iter().flatten());
        }
        let mut ordinal = 0_u64;
        loop {
            self.meter.node()?;
            let suffix = ordinal.to_string();
            let id = MVarId(Name::from_components([
                "_fln_unify_pruned",
                suffix.as_str(),
            ]));
            if !reserved.contains(&id) {
                return Ok(id);
            }
            ordinal = ordinal
                .checked_add(1)
                .ok_or(UnificationError::ExpressionScope)?;
        }
    }
}
