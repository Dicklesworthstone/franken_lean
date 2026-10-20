//! Quantified propositions retain their binders after body rewriting. The
//! family equality is ordinary function extensionality; applying the forall
//! selector transports it back into an equality of propositions.
use super::*;

impl Context {
    pub(super) fn simp_known_proposition(
        &mut self,
        expression: &Expr,
    ) -> Result<bool, NatDefinitionElabError> {
        let Some(sort) = self.known_type(expression)? else {
            return Ok(false);
        };
        let sort =
            self.whnf_with_transparency(&sort, UnificationTransparency::Abbreviations, false)?;
        if sort.has_expr_mvar() || sort.has_level_mvar() {
            return Ok(false);
        }
        // Reconstruction may retain imax u 0 rather than a literal zero.
        // Use the metered conversion engine, never an unbounded normalizer
        // or an assignment that guesses an unknown universe to be Prop.
        self.proof_types_match(&sort, &Expr::sort(Level::zero()))
    }

    pub(super) fn simp_close_forall(
        &mut self,
        frame: &BinderFrame,
        body: Expr,
        evidence: Typed,
    ) -> Result<(Expr, Typed), NatDefinitionElabError> {
        let ExprNode::ForallE {
            binder_name,
            binder_type,
            body: original_body,
            binder_info,
        } = frame.binder.node()
        else {
            return Err(error(TacticError::MalformedScript));
        };
        let family_frame = BinderFrame {
            parent: frame.parent,
            root: frame.root.clone(),
            binder: Expr::lam(
                binder_name.clone(),
                binder_type.clone(),
                original_body.clone(),
                *binder_info,
            ),
            local: frame.local.clone(),
            outer: frame.outer.clone(),
            inner: frame.inner.clone(),
        };
        let (next_family, equality) = self.simp_close_lambda(&family_frame, body, evidence)?;
        let ExprNode::Lam { body, .. } = next_family.node() else {
            unreachable!("lambda closing preserves its binder")
        };
        let next = Expr::forall_e(
            binder_name.clone(),
            binder_type.clone(),
            body.clone(),
            *binder_info,
        );
        let (_, family_type, _, _) =
            equality_target(&equality.type_).ok_or_else(|| error(TacticError::ExpectedEquality))?;
        let family = self.equality_local(family_type)?;
        let body = Expr::app(
            Expr::fvar(family.id.clone()),
            Expr::fvar(frame.local.id.clone()),
        );
        let selector = self.close_equality_binder(&frame.local, body, false)?;
        let selector = self.close_equality_binder(&family, selector, true)?;
        let prop = Expr::sort(Level::zero());
        let value = self
            .selector_congruence(&equality, &prop, &Level::one(), &selector)?
            .value;
        Ok((
            next.clone(),
            Typed {
                value,
                type_: equality::equation(Level::one(), prop, frame.binder.clone(), next),
            },
        ))
    }

    /// The same restricted reflexivity policy used at the top-level goal,
    /// applied under a heap-managed telescope. No arbitrary local assumption
    /// or unselected definition is used to complete a quantified proposition.
    pub(in crate::source::tactics::rewrite::simplify) fn simp_quantified_reflexivity(
        &mut self,
        goal: &ProofGoal,
        mut target: Expr,
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        let before = self.rewrite_trial();
        let result = (|| {
            self.txn.lctx = goal.lctx.clone();
            if !self.simp_known_proposition(&target)? {
                return Ok(None);
            }
            let mut locals = Vec::new();
            loop {
                self.tick()?;
                target = self.whnf_with_transparency(
                    &target,
                    UnificationTransparency::Abbreviations,
                    false,
                )?;
                let ExprNode::ForallE {
                    binder_type,
                    body,
                    binder_info,
                    ..
                } = target.node()
                else {
                    break;
                };
                let mut local = self.equality_local(binder_type.clone())?;
                local.binder_info = *binder_info;
                let body = self.substitute(body, &Expr::fvar(local.id.clone()))?;
                eliminate::add_local(&mut self.txn.lctx, &local);
                locals.push(local);
                target = body;
            }
            let mut value = if matches!(target.node(), ExprNode::Const { name, levels }
                if name == &Name::from_components(["True"]) && levels.is_empty())
            {
                self.constant(&Name::from_components(["True", "intro"]))?
                    .value
            } else {
                let leaf = ProofGoal {
                    id: goal.id.clone(),
                    target,
                    lctx: self.txn.lctx.clone(),
                    introduced: Vec::new(),
                };
                let Some(value) = self.automatic_reflexivity_candidate(&leaf, false)? else {
                    return Ok(None);
                };
                value
            };
            for local in locals.iter().rev() {
                value = self.close_equality_binder(local, value, true)?;
            }
            self.txn.lctx = before.txn.lctx.clone();
            Ok(Some(value))
        })();
        if !matches!(result, Ok(Some(_))) {
            self.restore_simp_trial(before);
        }
        result
    }
}
