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

    /// Whether `rules` rewrite `α → True` to `True`, as the pin's `implies_true`
    /// (`Init/SimpLemmas.lean:279`) does. Only such a rule takes the pin's simp from a
    /// quantified result to `True`: under binders a reflexive leaf becomes `True` by `eq_self`,
    /// which even `simp only` adds (`simpOnlyBuiltins`, `Lean/Elab/Tactic/Simp.lean:512`), and
    /// `∀ y, True` is then left unsolved. A rule counts when it is a global selected forward
    /// whose statement is `implies_true`'s; an applied instance (`implies_true Nat`) or a local
    /// is not recognized, so such a set leaves the quantified goal open. Only an environment
    /// without `eq_self` (the source seed) asks; elsewhere `implies_true` rewrites as a rule.
    pub(in crate::source::tactics::rewrite::simplify) fn simp_rules_close_implications(
        &mut self,
        rules: &[SimpRule<'_>],
    ) -> Result<bool, NatDefinitionElabError> {
        for rule in rules {
            let resolved;
            let name = match rule {
                SimpRule::Global(entry) if !entry.reverse => {
                    entry.proof.as_ref().unwrap_or(&entry.declaration)
                }
                SimpRule::Explicit(explicit) if !explicit.reverse => {
                    let Some(name) = self.simp_rule_global(explicit.syntax)? else {
                        continue;
                    };
                    resolved = name;
                    &resolved
                }
                _ => continue,
            };
            if self
                .txn
                .env
                .find(name)
                .is_some_and(|info| implies_true_statement(&info.constant_val().type_))
            {
                return Ok(true);
            }
        }
        Ok(false)
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
                    no_implicit_lambda: false,
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

/// `implies_true`'s statement, `∀ (α : Sort u), (α → True) = True` (`Init/SimpLemmas.lean:279`),
/// read from a declaration's type.
fn implies_true_statement(type_: &Expr) -> bool {
    let is_true = |expr: &Expr| {
        matches!(expr.node(), ExprNode::Const { name, levels }
            if levels.is_empty() && *name == Name::from_components(["True"]))
    };
    let ExprNode::ForallE {
        binder_type, body, ..
    } = type_.node()
    else {
        return false;
    };
    let Some((level, domain, left, right)) = equality_target(body) else {
        return false;
    };
    // A source declaration may state the domain as `Sort (imax u 0)`, the arrow's inferred sort.
    matches!(binder_type.node(), ExprNode::Sort { level } if matches!(level.view(), LevelView::Param(_)))
        && level.normalize() == Level::one()
        && matches!(domain.node(), ExprNode::Sort { level } if level.normalize().is_zero())
        && matches!(left.node(), ExprNode::ForallE { binder_type, body, .. }
            if matches!(binder_type.node(), ExprNode::BVar { idx: 0 }) && is_true(body))
        && is_true(&right)
}
