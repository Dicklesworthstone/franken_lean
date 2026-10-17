//! The pin's final `implies_congr` fallback, built from ordinary Eq.rec.
//! Both endpoints must be nondependent arrows. Transport the domain and
//! codomain independently; no function extensionality or new axiom is needed.
use super::*;

impl Context {
    pub(super) fn congruence_implication(
        &mut self,
        equation: &Equation,
    ) -> Result<Option<(Expr, Vec<ProofGoal>)>, NatDefinitionElabError> {
        self.tick()?;
        let left = self.whnf(&equation.left)?;
        let right = self.whnf(&equation.right)?;
        let (
            ExprNode::ForallE {
                binder_type: left_domain,
                body: left_range,
                ..
            },
            ExprNode::ForallE {
                binder_type: right_domain,
                body: right_range,
                ..
            },
        ) = (left.node(), right.node())
        else {
            return Ok(None);
        };
        // A dependent Pi cannot be replaced by a plain implication: the
        // codomain would escape its binder and the transport motive be false.
        if left_range.has_loose_bvars() || right_range.has_loose_bvars() {
            return Ok(None);
        }
        let mut premises = Vec::with_capacity(2);
        for (left, right) in [(left_domain, right_domain), (left_range, right_range)] {
            self.tick()?;
            let Some(domain) = self.known_type(left)? else {
                return Ok(None);
            };
            let Some(other) = self.known_type(right)? else {
                return Ok(None);
            };
            let budget = UnificationBudget::new(self.kernel);
            if !self.proof_types_match_with_budget(&domain, &other, budget)? {
                return Ok(None);
            }
            premises.push(Equation {
                level: self.congruence_sort(&domain)?,
                domain,
                left: left.clone(),
                right: right.clone(),
            });
        }
        let mut children = Vec::with_capacity(2);
        let mut value = equality::reflexivity(
            equation.level.clone(),
            equation.domain.clone(),
            equation.left.clone(),
        );
        for (index, premise) in premises.iter().enumerate() {
            self.tick()?;
            let (evidence, child) = self.proof_goal(premise.target())?;
            children.push(child);
            value = self.congruence_transport(
                premise,
                evidence,
                |point| {
                    let (domain, range) = if index == 0 {
                        (point, left_range.clone())
                    } else {
                        (right_domain.clone(), point)
                    };
                    let arrow =
                        Expr::forall_e(Name::anonymous(), domain, range, BinderInfo::Default);
                    equality::equation(
                        equation.level.clone(),
                        equation.domain.clone(),
                        equation.left.clone(),
                        arrow,
                    )
                },
                value,
            )?;
        }
        Ok(Some((value, children)))
    }
}
