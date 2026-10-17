//! `guard_hyp` checks the live context; it cannot solve or admit a proof.
//!
//! The contract is `evalGuardHyp` in the pinned Lean/Elab/Tactic/Guard.lean:
//! optional type checks are elaborated without an expected type, value checks
//! use the local's type, and a let must have a value clause. Each comparison
//! restores its speculative assignments while retaining the work it spent.

use super::*;

fn clause(
    syntax: &Syntax,
    value: bool,
) -> Result<Option<(guard::Relation, &Syntax)>, NatDefinitionElabError> {
    let parts = expect_null_args(syntax, "guard_hyp optional clause")?;
    let [relation, term] = parts else {
        return if parts.is_empty() {
            Ok(None)
        } else {
            Err(error(TacticError::MalformedScript))
        };
    };
    let (category, kinds, spellings) = if value {
        (
            "colonEq",
            ["colonEqR", "colonEqD", "colonEqS", "colonEqA"],
            [":=", ":=~", ":=ₛ", ":=ₐ"],
        )
    } else {
        (
            "colon",
            ["colonR", "colonD", "colonS", "colonA"],
            [":", ":~", ":ₛ", ":ₐ"],
        )
    };
    let [relation] = expect_node(relation, &parser_kind(&[category]), 1, "guard_hyp relation")?
    else {
        return Err(error(TacticError::MalformedScript));
    };
    let Syntax::Node { kind, args, .. } = relation else {
        return Err(error(TacticError::MalformedScript));
    };
    let index = kinds
        .iter()
        .position(|name| kind == &parser_kind(&[*name]))
        .ok_or_else(|| error(TacticError::MalformedScript))?;
    let [atom] = args.as_slice() else {
        return Err(error(TacticError::MalformedScript));
    };
    expect_atom(atom, spellings[index], "guard_hyp relation")?;
    let relation = match index {
        0 => guard::Relation::DefEq(UnificationTransparency::Abbreviations),
        1 => guard::Relation::DefEq(UnificationTransparency::Default),
        2 => guard::Relation::Syntactic,
        _ => guard::Relation::Alpha,
    };
    Ok(Some((relation, term)))
}

impl Context {
    pub(super) fn guard_hypothesis(
        &mut self,
        goal: &ProofGoal,
        args: &[Syntax],
    ) -> Result<(), NatDefinitionElabError> {
        let [keyword, subject, type_slot, value_slot] = args else {
            return Err(error(TacticError::MalformedScript));
        };
        expect_atom(keyword, "guard_hyp", "guard_hyp keyword")?;
        self.require_declared_tactic(&["Lean", "Parser", "Tactic", "guardHyp"])?;
        let type_clause = clause(type_slot, false)?;
        let value_clause = clause(value_slot, true)?;
        self.txn.lctx = goal.lctx.clone();
        let subject = self.term(subject, None)?;
        let mut subject = self.instantiate(&subject.value)?;
        while let ExprNode::MData { expr, .. } = subject.node() {
            self.tick()?;
            subject = expr.clone();
        }
        // Resolve the elaborated local identity, not its spelling. This handles
        // shadowing and parentheses, and rejects constants and projections.
        let mut found = None;
        for local in goal.lctx.decls().iter().rev() {
            self.tick()?;
            if !self.is_matrix_hypothesis(local) && subject == Expr::fvar(local.id.clone()) {
                found = Some(local.clone());
                break;
            }
        }
        let local = found.ok_or_else(|| error(TacticError::GuardHypExpectedLocal))?;
        if let Some((relation, expected)) = type_clause {
            let value = self.guard_hyp_term(expected, None)?;
            let type_ = self.instantiate(&local.type_)?;
            if !self.guard_hyp_compare(&value, &type_, relation)? {
                return Err(error(TacticError::GuardHypTypeMismatch(local.user_name)));
            }
        }
        match (&local.value, value_clause) {
            (None, None) => Ok(()),
            (None, Some(_)) => Err(error(TacticError::GuardHypNotLet(local.user_name))),
            (Some(_), None) => Err(error(TacticError::GuardHypMissingValue(local.user_name))),
            (Some(actual), Some((relation, expected))) => {
                let type_ = self.instantiate(&local.type_)?;
                let value = self.guard_hyp_term(expected, Some(type_))?;
                let actual = self.instantiate(actual)?;
                if self.guard_hyp_compare(&value, &actual, relation)? {
                    Ok(())
                } else {
                    Err(error(TacticError::GuardHypValueMismatch(local.user_name)))
                }
            }
        }
    }

    fn guard_hyp_term(
        &mut self,
        syntax: &Syntax,
        expected: Option<Expr>,
    ) -> Result<Expr, NatDefinitionElabError> {
        let term = self.term(syntax, expected)?;
        // As in guard_target, Tactic.elabTerm synthesizes before comparing,
        // including the default instances needed by literal arguments.
        self.resolve_instances(false)?;
        self.flush(false)?;
        self.resolve_instances_with_defaults()?;
        self.flush(false)?;
        self.instantiate(&term.value)
    }

    fn guard_hyp_compare(
        &mut self,
        left: &Expr,
        right: &Expr,
        relation: guard::Relation,
    ) -> Result<bool, NatDefinitionElabError> {
        self.tick()?;
        let snapshot = self.clone();
        let result = self.guard_expr_matches(left, right, relation);
        let spent = self.txn.budget.heartbeats_consumed;
        *self = snapshot;
        self.txn.budget.heartbeats_consumed = spent;
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn context() -> Context {
        let budget = Budget::for_stack_bytes(2 * 1024 * 1024);
        let env = seed::bootstrap_nat_environment(budget).unwrap();
        Context::new(&env, budget)
    }

    #[test]
    fn a_successful_comparison_restores_assignments_but_keeps_spent_work() {
        let mut context = context();
        let nat = Expr::const_(Name::from_components(["Nat"]), Vec::new());
        let hole = context.hole(nat).unwrap();
        let seven = Expr::lit(Literal::Nat(fln_core::expr::NatLit::from_u64(7)));
        let spent = context.txn.budget.heartbeats_consumed;
        assert!(
            context
                .guard_hyp_compare(
                    &hole,
                    &seven,
                    guard::Relation::DefEq(UnificationTransparency::Abbreviations),
                )
                .unwrap()
        );
        assert!(context.txn.budget.heartbeats_consumed > spent);
        assert_eq!(context.instantiate(&hole).unwrap(), hole);
    }

    #[test]
    fn exhaustion_is_not_a_failed_guard_that_first_can_catch() {
        let mut context = context();
        context.txn.budget.max_heartbeats = 1;
        let one = Expr::lit(Literal::Nat(fln_core::expr::NatLit::from_u64(1)));
        let problem = context
            .guard_hyp_compare(&one, &one, guard::Relation::Alpha)
            .unwrap_err();
        assert!(matches!(
            problem,
            NatDefinitionElabError::Inference(SourceInferenceError::ResourceLimit)
        ));
        assert!(!backtrack::recoverable(&problem));
    }
}
