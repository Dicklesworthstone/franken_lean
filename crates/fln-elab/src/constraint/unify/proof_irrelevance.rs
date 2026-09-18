//! Proof irrelevance for the native equation worklist (plan §10.2).
//!
//! Candidate type synthesis only selects this rung. K1 checks an application
//! of `(fun (P : Prop) (x y : P) => x)` to the original proposition and BOTH
//! proofs before the equation can disappear. This checks `P : Prop` and each
//! proof's type, rather than mistaking a syntactic result type for evidence.
//! No proof metavariable is assigned or generalized here. Open proof obligations
//! stay open; later assignments can make a postponed equation checkable.
use super::*;
use fln_core::expr::BinderInfo;

impl Engine<'_> {
    pub(super) fn proof_irrelevance(
        &mut self,
        left: &Expr,
        right: &Expr,
        locals: &LocalContext,
    ) -> Result<bool, UnificationError> {
        // Lambda/lambda comparison already opens a shared typed binder. A
        // lambda/neutral comparison can use the neutral's inferred Pi type.
        let candidate = match self.eta_neutral_type(left, locals)? {
            Some(type_) => Some(type_),
            None => self.eta_neutral_type(right, locals)?,
        };
        let Some(proposition) = candidate else {
            return Ok(false);
        };
        // Avoid sending ordinary data equations to K1. A Pi can itself be a
        // proposition by impredicativity; the guard checks that, not this hint.
        if !matches!(proposition.node(), ExprNode::ForallE { .. }) {
            let Some(sort) = self.eta_neutral_type(&proposition, locals)? else {
                return Ok(false);
            };
            let ExprNode::Sort { level } = sort.node() else {
                return Ok(false);
            };
            let level = normalize::simplify(level, &mut self.meter)?;
            if !level.is_zero() {
                return Ok(false);
            }
        }
        let proposition = self.instantiate(&proposition)?;
        let left = self.instantiate(left)?;
        let right = self.instantiate(right)?;
        if [&proposition, &left, &right]
            .iter()
            .any(|term| term.has_expr_mvar() || term.has_level_mvar() || term.has_loose_bvars())
        {
            // Proof irrelevance never solves a proof hole by erasing it.
            return Ok(false);
        }
        self.check_proof_pair(proposition, left, right, locals)
    }

    fn check_proof_pair(
        &mut self,
        mut type_: Expr,
        left: Expr,
        right: Expr,
        locals: &LocalContext,
    ) -> Result<bool, UnificationError> {
        let bv = |index| Expr::bvar(index).expect("fixed proof guard indices pack");
        let anonymous = Name::anonymous();
        let guard = Expr::lam(
            anonymous.clone(),
            Expr::sort(Level::zero()),
            Expr::lam(
                anonymous.clone(),
                bv(0),
                Expr::lam(anonymous, bv(1), bv(1), BinderInfo::Default),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        );
        let mut value = Expr::app(Expr::app(Expr::app(guard, type_.clone()), left), right);
        // Close the exact context, retaining lets as lets. Replacing a local's
        // declared type by the type of that type would change the judgment.
        let mut seen = HashSet::new();
        for local in locals.decls().iter().rev() {
            self.meter.node()?;
            if !seen.insert(local.id.clone()) {
                return Ok(false);
            }
            self.scan(&type_)?;
            self.scan(&value)?;
            type_ = type_
                .abstract_fvar(&local.id, 0)
                .map_err(|_| UnificationError::ExpressionScope)?;
            value = value
                .abstract_fvar(&local.id, 0)
                .map_err(|_| UnificationError::ExpressionScope)?;
            let domain = self.instantiate(&local.type_)?;
            if let Some(local_value) = &local.value {
                let local_value = self.instantiate(local_value)?;
                type_ = Expr::let_e(
                    local.user_name.clone(),
                    domain.clone(),
                    local_value.clone(),
                    type_,
                    false,
                );
                value = Expr::let_e(local.user_name.clone(), domain, local_value, value, false);
            } else {
                type_ = Expr::forall_e(
                    local.user_name.clone(),
                    domain.clone(),
                    type_,
                    local.binder_info,
                );
                value = Expr::lam(local.user_name.clone(), domain, value, local.binder_info);
            }
        }
        if [&type_, &value]
            .iter()
            .any(|term| term.has_expr_mvar() || term.has_level_mvar() || term.has_loose_bvars())
        {
            return Ok(false);
        }
        let type_facts = self.scan(&type_)?;
        let value_facts = self.scan(&value)?;
        if !type_facts.fvars.is_empty() || !value_facts.fvars.is_empty() {
            return Ok(false);
        }
        let mut parameters = type_facts.params;
        for parameter in value_facts.params {
            self.meter.node()?;
            if !parameters.contains(&parameter) {
                parameters.push(parameter);
            }
        }
        let mut ordinal = 0_u64;
        let name = loop {
            self.meter.tick()?;
            let name = Name::num(
                Name::from_components(["_fln_proof_irrelevance_check"]),
                ordinal,
            );
            if !self.work.env.contains(&name) {
                break name;
            }
            ordinal = ordinal
                .checked_add(1)
                .ok_or(UnificationError::ExpressionScope)?;
        };
        let declaration = Declaration::Defn(DefinitionVal {
            base: ConstantVal {
                name: name.clone(),
                level_params: parameters,
                type_,
            },
            value,
            hints: ReducibilityHints::Regular(1),
            safety: DefinitionSafety::Safe,
            all: vec![name],
        });
        self.meter.tick()?;
        self.kernel_checks += 1;
        match check(&self.work.env, &declaration, self.budget.kernel) {
            Outcome::Complete(Verdict::Accepted { .. }) => Ok(true),
            Outcome::Complete(Verdict::Rejected { .. }) => Ok(false),
            outcome => Err(UnificationError::ConversionCheck {
                outcome: Box::new(outcome),
            }),
        }
    }
}
