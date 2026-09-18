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
        pending: &mut VecDeque<Equation>,
    ) -> Result<bool, UnificationError> {
        // Neutral synthesis is a hint; the final guard still checks BOTH original
        // proofs. In particular, synthesizing an application type does not prove
        // that its arguments are well-typed.
        let left_type = self.eta_neutral_type(left, locals)?;
        // A known non-proof type rules this rung out. In particular, do not
        // reconstruct the other side's entire recursor telescope for each
        // impossible rewrite occurrence. The final guard is unchanged for
        // every pair that can actually select proof irrelevance.
        if let Some(type_) = &left_type
            && !self.proof_type_is_prop(type_, locals)?
        {
            return Ok(false);
        }
        let right_type = self.eta_neutral_type(right, locals)?;
        let Some(proposition) = left_type.as_ref().or(right_type.as_ref()) else {
            return Ok(false);
        };
        // A Pi can itself be a proposition by impredicativity. Opening its
        // codomain also lets type-directed inference work below dependent binders.
        if left_type.is_none() && !self.proof_type_is_prop(proposition, locals)? {
            return Ok(false);
        }
        if let (Some(left_type), Some(right_type)) = (&left_type, &right_type) {
            let left_type = self.instantiate(left_type)?;
            let right_type = self.instantiate(right_type)?;
            if (left_type.has_expr_mvar()
                || left_type.has_level_mvar()
                || right_type.has_expr_mvar()
                || right_type.has_level_mvar())
                && !same_terms(&left_type, &right_type, &mut self.meter)?
                && self.proof_type_is_prop(&right_type, locals)?
            {
                // Generate an ordinary equation, NOT a successful proof verdict.
                // The original proof pair is postponed by the outer worklist and
                // must return through check_proof_pair after assignments advance.
                // If no generation advances, the normal fixed-point rule defers;
                // there is no recursively re-entered solver or unbounded retry.
                pending.push_front((left_type, right_type, locals.clone()));
                return Err(UnificationError::Deferred(
                    UnificationDeferred::UnsupportedEquation,
                ));
            }
        }
        let proposition = self.instantiate(proposition)?;
        let left = self.instantiate(left)?;
        let right = self.instantiate(right)?;
        if [&proposition, &left, &right]
            .iter()
            .any(|term| term.has_expr_mvar() || term.has_level_mvar() || term.has_loose_bvars())
        {
            // Type inference cannot erase a residual proof obligation.
            return Ok(false);
        }
        self.check_proof_pair(proposition, left, right, locals)
    }

    /// A metered selection hint, never a typing judgment. A definite Prop result
    /// is required: this cannot default an unknown universe to zero. Domains and
    /// application arguments are validated later by the ordinary K1 guard.
    fn proof_type_is_prop(
        &mut self,
        proposition: &Expr,
        locals: &LocalContext,
    ) -> Result<bool, UnificationError> {
        let mut type_ = self.instantiate(proposition)?;
        let mut context = locals.clone();
        loop {
            self.meter.node()?;
            type_ = self.whnf(&type_, &context)?;
            if let ExprNode::ForallE {
                binder_type,
                body,
                binder_info,
                ..
            } = type_.node()
            {
                let id = self.fresh()?;
                let argument = Expr::fvar(id.clone());
                let domain = self.instantiate(binder_type)?;
                let body = self.substitute(body, &argument)?;
                context.add_param(id.clone(), id.0, domain, *binder_info);
                type_ = body;
                continue;
            }
            let Some(sort) = self.eta_neutral_type(&type_, &context)? else {
                return Ok(false);
            };
            let ExprNode::Sort { level } = sort.node() else {
                return Ok(false);
            };
            return Ok(normalize::simplify(level, &mut self.meter)?.is_zero());
        }
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
