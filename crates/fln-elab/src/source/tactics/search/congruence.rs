//! Structural instances of the pin's default congrFun/congrArg rules.
//! Each produces an ordinary equality premise and an Eq.rec continuation.
//! No equality is inferred from application shape alone, and congrArg's
//! common function must have a genuinely nondependent codomain.
use super::*;

impl Context {
    pub(super) fn search_congruence_candidate(
        &mut self,
        goal: &ProofGoal,
        function: bool,
    ) -> Result<Vec<Work<'static>>, NatDefinitionElabError> {
        self.txn.lctx = goal.lctx.clone();
        self.tick()?;
        let target = self.whnf(&goal.target)?;
        let Some((level, codomain, left, right)) = equality_target(&target) else {
            return Err(error(TacticError::NoMatchingAssumption));
        };
        let (ExprNode::App { f, a }, ExprNode::App { f: g, a: b }) = (left.node(), right.node())
        else {
            return Err(error(TacticError::NoMatchingAssumption));
        };
        let Some(function_type) = self.known_type(f)? else {
            return Err(error(TacticError::NoMatchingAssumption));
        };
        let function_type = self.whnf(&function_type)?;
        let ExprNode::ForallE { binder_type, .. } = function_type.node() else {
            return Err(error(TacticError::NoMatchingAssumption));
        };
        let (domain, lhs, rhs, selector) = if function {
            // congrFun permits a dependent result family, but its argument
            // is the same at both endpoints. Transport the function itself.
            if !self.coercion_eq(a, b)? {
                return Err(error(TacticError::NoMatchingAssumption));
            }
            let Some(other_type) = self.known_type(g)? else {
                return Err(error(TacticError::NoMatchingAssumption));
            };
            if !self.coercion_eq(&function_type, &other_type)? {
                return Err(error(TacticError::NoMatchingAssumption));
            }
            let local = self.equality_local(function_type.clone())?;
            let value = Expr::app(Expr::fvar(local.id.clone()), a.clone());
            let selector = self.close_equality_binder(&local, value, true)?;
            (function_type, f.clone(), g.clone(), selector)
        } else {
            // Endpoint result types being equal is insufficient: a dependent
            // family may coincide only at those endpoints. Check the complete
            // function telescope against a constant-codomain function before
            // building its motive. Conversion may expose a reducible alias.
            if !self.coercion_eq(f, g)? {
                return Err(error(TacticError::NoMatchingAssumption));
            }
            let expected = Expr::forall_e(
                Name::anonymous(),
                binder_type.clone(),
                codomain.clone(),
                BinderInfo::Default,
            );
            if !self.coercion_eq(&function_type, &expected)? {
                return Err(error(TacticError::NoMatchingAssumption));
            }
            (binder_type.clone(), a.clone(), b.clone(), f.clone())
        };
        let Some(sort) = self.known_type(&domain)? else {
            return Err(error(TacticError::NoMatchingAssumption));
        };
        let universe = self.sort_level(&Typed {
            value: domain.clone(),
            type_: sort,
        })?;
        let premise = equality::equation(universe, domain, lhs, rhs);
        let (evidence, child) = self.proof_goal(premise.clone())?;
        let result = self.selector_congruence(
            &Typed {
                value: evidence,
                type_: premise,
            },
            &codomain,
            &level,
            &selector,
        )?;
        Ok(vec![
            Work::Close(goal.clone(), result.value),
            Work::Goal(child),
        ])
    }
}
