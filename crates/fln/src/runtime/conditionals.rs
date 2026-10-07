//! Preserve the pin's lazy `ite`/`dite` code generation contract.
//!
//! These Prelude functions are macro-inlined before strict argument evaluation.
//! Unfold only a verified complete logical model, while the original proof
//! context still exists; the ordinary Decidable recursor supplies native lazy
//! branches and its usual checked-family representation guard.
use super::*;
use fln_env::constants::DefinitionSafety;

#[cfg(test)]
mod tests;

impl Preparation<'_> {
    fn canonical_decision_cases_on(&mut self) -> Result<bool, IngressError> {
        use fln_core::level::Level;
        let label = name("Decidable.casesOn");
        let Some(ConstantInfo::Defn(actual)) = self.environment.find(&label) else {
            return Ok(false);
        };
        let actual = actual.clone();
        let u = name("u");
        if actual.safety != DefinitionSafety::Safe
            || actual.base.level_params != [u.clone()]
            || actual.all != [label]
        {
            return Ok(false);
        }
        let b = |index| Expr::bvar(index).expect("fixed casesOn telescope");
        let c = |label| Expr::const_(name(label), vec![]);
        let apply = |head, args: Vec<Expr>| args.into_iter().fold(head, Expr::app);
        let pi =
            |domain, body| Expr::forall_e(Name::anonymous(), domain, body, BinderInfo::Default);
        let lambda = |domain, body| Expr::lam(Name::anonymous(), domain, body, BinderInfo::Default);
        let binders = [
            (Expr::sort(Level::zero()), BinderInfo::Implicit),
            (
                pi(
                    Expr::app(c("Decidable"), b(0)),
                    Expr::sort(Level::param(u.clone())),
                ),
                BinderInfo::Implicit,
            ),
            (Expr::app(c("Decidable"), b(1)), BinderInfo::Default),
            (
                pi(
                    Expr::app(c("Not"), b(2)),
                    Expr::app(b(2), apply(c("Decidable.isFalse"), vec![b(3), b(0)])),
                ),
                BinderInfo::Default,
            ),
            (
                pi(
                    b(3),
                    Expr::app(b(3), apply(c("Decidable.isTrue"), vec![b(4), b(0)])),
                ),
                BinderInfo::Default,
            ),
        ];
        let mut type_ = Expr::app(b(3), b(2));
        let mut value = apply(
            Expr::const_(name("Decidable.rec"), vec![Level::param(u)]),
            vec![
                b(4),
                b(3),
                lambda(Expr::app(c("Not"), b(4)), Expr::app(b(2), b(0))),
                lambda(b(4), Expr::app(b(1), b(0))),
                b(2),
            ],
        );
        for (domain, info) in binders.into_iter().rev() {
            self.tick()?;
            type_ = Expr::forall_e(Name::anonymous(), domain.clone(), type_, info);
            value = Expr::lam(Name::anonymous(), domain, value, info);
        }
        Ok(crate::olean_imports::expr_eqv(&actual.base.type_, &type_)
            && crate::olean_imports::expr_eqv(&actual.value, &value))
    }

    pub(super) fn lazy_conditional(
        &mut self,
        head: &Expr,
        arguments: &[Expr],
    ) -> Result<Option<Expr>, IngressError> {
        let ExprNode::Const {
            name: callee,
            levels,
        } = head.node()
        else {
            return Ok(None);
        };
        let dependent = if callee == &name("ite") {
            false
        } else if callee == &name("dite") {
            true
        } else {
            return Ok(None);
        };
        if levels.len() != 1 || arguments.len() < 5 {
            return Ok(None);
        }
        let Some(ConstantInfo::Defn(actual)) = self.environment.find(callee).cloned() else {
            return Ok(None);
        };
        let index = usize::from(dependent);
        if !self.conditional_contracts[index] {
            let Some(Declaration::Defn(expected)) = fln_elab::seed::source_seed_declarations()
                .into_iter()
                .find(|declaration| {
                    matches!(declaration, Declaration::Defn(definition)
                        if definition.base.name == *callee)
                })
            else {
                return Err(unsupported("conditional logical model"));
            };
            self.tick()?;
            if actual.safety != DefinitionSafety::Safe
                || actual.base.level_params != expected.base.level_params
                || actual.all != expected.all
                || !crate::olean_imports::expr_eqv(&actual.base.type_, &expected.base.type_)
            {
                return Ok(None);
            }
            let mut actual_body = actual.value.clone();
            let mut expected_body = expected.value;
            for _ in 0..5 {
                self.tick()?;
                let (
                    ExprNode::Lam {
                        binder_type: actual_type,
                        body: actual_next,
                        binder_info: actual_info,
                        ..
                    },
                    ExprNode::Lam {
                        binder_type: expected_type,
                        body: expected_next,
                        binder_info: expected_info,
                        ..
                    },
                ) = (actual_body.node(), expected_body.node())
                else {
                    return Ok(None);
                };
                if actual_info != expected_info
                    || !crate::olean_imports::expr_eqv(actual_type, expected_type)
                {
                    return Ok(None);
                }
                actual_body = actual_next.clone();
                expected_body = expected_next.clone();
            }
            // The Prelude writes casesOn; the seed writes its recursor.
            // Compare each complete shape without beta, delta or zeta
            // reduction: a strict unused computation is not this contract.
            if !crate::olean_imports::expr_eqv(&actual_body, &expected_body) {
                let (recursor, parts) = self.spine(&expected_body)?;
                let ExprNode::Const {
                    levels: recursor_levels,
                    ..
                } = recursor.node()
                else {
                    return Err(unsupported("conditional recursor model"));
                };
                if parts.len() != 5 {
                    return Err(unsupported("conditional recursor model"));
                }
                let expected_cases_on = [0, 1, 4, 2, 3].into_iter().fold(
                    Expr::const_(name("Decidable.casesOn"), recursor_levels.clone()),
                    |head, index| Expr::app(head, parts[index].clone()),
                );
                if !crate::olean_imports::expr_eqv(&actual_body, &expected_cases_on)
                    || !self.canonical_decision_cases_on()?
                {
                    return Ok(None);
                }
            }
            self.conditional_contracts[index] = true;
        }
        let mut body = self.universe_instance(&actual.value, &actual.base.level_params, levels)?;
        for argument in &arguments[..5] {
            self.tick()?;
            let ExprNode::Lam { body: next, .. } = body.node() else {
                return Err(unsupported("conditional lambda telescope"));
            };
            body = self.substitution(next, argument)?;
        }
        for argument in &arguments[5..] {
            self.tick()?;
            body = Expr::app(body, argument.clone());
        }
        Ok(Some(body))
    }
}
