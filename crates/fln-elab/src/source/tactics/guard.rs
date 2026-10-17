//! `guard_target` (`syntax (name := guardTarget) "guard_target " equal term : tactic`,
//! Init/Guard.lean:75), as `evalGuardTarget` (Lean/Elab/Tactic/Guard.lean:99-110): the term is
//! elaborated against the type of the main goal's target, compared with the target by the chosen
//! relation, and the goal is left as it was. The comparison runs `withoutModifyingState`, so a
//! unification it makes is undone here too.
use super::*;

/// `MatchKind` (Lean/Elab/Tactic/Guard.lean:23-28), from the `equal` syntax (`:52-56`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Relation {
    /// `=ₛ`: `a.consumeMData == b.consumeMData`.
    Syntactic,
    /// `=ₐ`: `a.eqv b`.
    Alpha,
    /// `=` (reducible) and `=~` (default): `isDefEqGuarded` at that transparency.
    DefEq(UnificationTransparency),
}

pub(super) fn relation(syntax: &Syntax) -> Result<Relation, NatDefinitionElabError> {
    let parts = expect_node(syntax, &parser_kind(&["equal"]), 1, "guard_target relation")?;
    let Syntax::Node { kind, args, .. } = &parts[0] else {
        return Err(error(TacticError::MalformedScript));
    };
    let (relation, spelling) = if kind == &parser_kind(&["equalR"]) {
        (Relation::DefEq(UnificationTransparency::Abbreviations), "=")
    } else if kind == &parser_kind(&["equalD"]) {
        (Relation::DefEq(UnificationTransparency::Default), "=~")
    } else if kind == &parser_kind(&["equalS"]) {
        (Relation::Syntactic, "=ₛ")
    } else if kind == &parser_kind(&["equalA"]) {
        (Relation::Alpha, "=ₐ")
    } else {
        return Err(error(TacticError::MalformedScript));
    };
    let [atom] = args.as_slice() else {
        return Err(error(TacticError::MalformedScript));
    };
    expect_atom(atom, spelling, "guard_target relation")?;
    Ok(relation)
}

fn consume_mdata(mut expr: &Expr) -> &Expr {
    while let ExprNode::MData { expr: inner, .. } = expr.node() {
        expr = inner;
    }
    expr
}

impl Context {
    /// Whether the main goal's target matches `expected` by `relation`. The context is restored
    /// afterwards (the pin's `withoutModifyingState`); only the spent work is kept.
    pub(super) fn guard_target_matches(
        &mut self,
        goal: &ProofGoal,
        relation: Relation,
        expected: &Syntax,
    ) -> Result<bool, NatDefinitionElabError> {
        let snapshot = self.clone();
        let result = self.guard_target_check(goal, relation, expected);
        let spent = self.txn.budget.heartbeats_consumed;
        *self = snapshot;
        self.txn.budget.heartbeats_consumed = spent;
        result
    }

    fn guard_target_check(
        &mut self,
        goal: &ProofGoal,
        relation: Relation,
        expected: &Syntax,
    ) -> Result<bool, NatDefinitionElabError> {
        self.txn.lctx = goal.lctx.clone();
        let target = self.instantiate(&goal.target)?;
        let target_type = self
            .known_type(&target)?
            .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
        let elaborated = self.term(expected, Some(target_type))?;
        // `Tactic.elabTerm` synthesizes without postponing, default instances included, before
        // `isEq` compares: `guard_target = 1 = 1` meets the goal's `@OfNat.ofNat Nat 1 _`.
        self.resolve_instances(false)?;
        self.flush(false)?;
        self.resolve_instances_with_defaults()?;
        self.flush(false)?;
        let value = self.instantiate(&elaborated.value)?;
        self.guard_expr_matches(&value, &target, relation)
    }

    /// The shared guard comparison. Callers own the snapshot that prevents
    /// comparison-only assignments from changing the proof state.
    pub(super) fn guard_expr_matches(
        &mut self,
        value: &Expr,
        target: &Expr,
        relation: Relation,
    ) -> Result<bool, NatDefinitionElabError> {
        match relation {
            Relation::Syntactic => self.expr_eqv(consume_mdata(value), consume_mdata(target)),
            Relation::Alpha => self.expr_eqv(value, target),
            Relation::DefEq(transparency) => {
                let mut budget = UnificationBudget::new(self.kernel);
                budget.transparency = transparency;
                self.proof_types_match_with_budget(value, target, budget)
            }
        }
    }

    /// `Expr.eqv` (`lean_expr_eqv`): structural equality that ignores binder names and binder
    /// information, by an explicit worklist.
    fn expr_eqv(&mut self, left: &Expr, right: &Expr) -> Result<bool, NatDefinitionElabError> {
        let mut pending = vec![(left.clone(), right.clone())];
        while let Some((a, b)) = pending.pop() {
            self.tick()?;
            match (a.node(), b.node()) {
                (ExprNode::App { f: af, a: aa }, ExprNode::App { f: bf, a: ba }) => {
                    pending.push((af.clone(), bf.clone()));
                    pending.push((aa.clone(), ba.clone()));
                }
                (
                    ExprNode::Lam {
                        binder_type: at,
                        body: ab,
                        ..
                    },
                    ExprNode::Lam {
                        binder_type: bt,
                        body: bb,
                        ..
                    },
                )
                | (
                    ExprNode::ForallE {
                        binder_type: at,
                        body: ab,
                        ..
                    },
                    ExprNode::ForallE {
                        binder_type: bt,
                        body: bb,
                        ..
                    },
                ) => {
                    if matches!(a.node(), ExprNode::Lam { .. })
                        != matches!(b.node(), ExprNode::Lam { .. })
                    {
                        return Ok(false);
                    }
                    pending.push((at.clone(), bt.clone()));
                    pending.push((ab.clone(), bb.clone()));
                }
                (
                    ExprNode::LetE {
                        type_: at,
                        value: av,
                        body: ab,
                        ..
                    },
                    ExprNode::LetE {
                        type_: bt,
                        value: bv,
                        body: bb,
                        ..
                    },
                ) => {
                    pending.push((at.clone(), bt.clone()));
                    pending.push((av.clone(), bv.clone()));
                    pending.push((ab.clone(), bb.clone()));
                }
                (
                    ExprNode::MData { data: ad, expr: ae },
                    ExprNode::MData { data: bd, expr: be },
                ) => {
                    if ad != bd {
                        return Ok(false);
                    }
                    pending.push((ae.clone(), be.clone()));
                }
                (
                    ExprNode::Proj {
                        struct_name: an,
                        idx: ai,
                        expr: ae,
                    },
                    ExprNode::Proj {
                        struct_name: bn,
                        idx: bi,
                        expr: be,
                    },
                ) => {
                    if an != bn || ai != bi {
                        return Ok(false);
                    }
                    pending.push((ae.clone(), be.clone()));
                }
                // The remaining nodes bind nothing: plain equality is `eqv` for them.
                _ => {
                    if a != b {
                        return Ok(false);
                    }
                }
            }
        }
        Ok(true)
    }
}
