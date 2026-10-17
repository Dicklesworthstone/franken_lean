//! Classify erased type formers using the existing bounded source reducer.
//! Like the pin's typeFormerTypeLevel, reduce aliases in the actual telescope;
//! being an element of a universe is not sufficient evidence of erasure.
use super::*;

impl Context {
    pub(super) fn codegen_type_former(
        &mut self,
        type_: &Expr,
    ) -> Result<bool, NatDefinitionElabError> {
        let saved = self.txn.lctx.clone();
        let result = self.codegen_type_former_inner(type_);
        // Restore even if reduction/substitution/fresh-name allocation stops.
        // Work and fresh identities are spent, never rolled back into reuse.
        self.txn.lctx = saved;
        result
    }

    fn codegen_type_former_inner(&mut self, type_: &Expr) -> Result<bool, NatDefinitionElabError> {
        let mut cursor = type_.clone();
        loop {
            self.tick()?;
            // Default transparency preserves opaque, unsafe, partial and
            // irreducible barriers. Never unfold the executable VALUE here.
            let normal = self.whnf(&cursor)?;
            match normal.node() {
                ExprNode::Sort { .. } => return Ok(true),
                ExprNode::ForallE {
                    binder_name,
                    binder_type,
                    body,
                    binder_info,
                } => {
                    let id = FVarId(self.fresh_name()?);
                    self.txn.lctx.add_param(
                        id.clone(),
                        binder_name.clone(),
                        binder_type.clone(),
                        *binder_info,
                    );
                    cursor = self.substitute(body, &Expr::fvar(id))?;
                }
                // An abstract codomain, stuck reduction, or ordinary data
                // type has not demonstrated that its values can be erased.
                _ => return Ok(false),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn n(name: &str) -> Name {
        Name::from_components(name.split('.'))
    }
    fn telescope(result: Expr) -> Expr {
        Expr::forall_e(
            n("A"),
            Expr::sort(Level::one()),
            Expr::forall_e(n("x"), Expr::bvar(0).unwrap(), result, BinderInfo::Default),
            BinderInfo::Implicit,
        )
    }

    #[test]
    fn an_abstract_codomain_is_data_even_when_its_type_is_a_sort() {
        let env = crate::seed::bootstrap_nat_environment(Budget::DEFAULT).unwrap();
        let mut context = Context::new(&env, Budget::DEFAULT);
        let saved = context.txn.lctx.clone();
        assert!(
            !context
                .codegen_type_former(&telescope(Expr::bvar(1).unwrap()))
                .unwrap()
        );
        assert!(
            context
                .codegen_type_former(&telescope(Expr::sort(Level::one())))
                .unwrap()
        );
        assert!(
            context
                .codegen_type_former(&telescope(Expr::sort(Level::zero())))
                .unwrap()
        );
        assert_eq!(context.txn.lctx, saved);
        assert_eq!(context.txn.env, env);
    }

    #[test]
    fn type_former_analysis_uses_the_existing_let_context_without_leaking_binders() {
        let env = crate::seed::bootstrap_nat_environment(Budget::DEFAULT).unwrap();
        let mut context = Context::new(&env, Budget::DEFAULT);
        let id = FVarId(n("localUniverse"));
        context.txn.lctx.add_let(
            id.clone(),
            n("U"),
            Expr::sort(Level::succ(Level::one()).unwrap()),
            Expr::sort(Level::one()),
        );
        let saved = context.txn.lctx.clone();
        assert!(
            context
                .codegen_type_former(&telescope(Expr::fvar(id)))
                .unwrap()
        );
        assert_eq!(context.txn.lctx, saved);
    }

    #[test]
    fn every_type_former_budget_stop_restores_the_original_telescope() {
        let env = crate::seed::bootstrap_nat_environment(Budget::DEFAULT).unwrap();
        let expr = telescope(Expr::let_e(
            n("U"),
            Expr::sort(Level::succ(Level::one()).unwrap()),
            Expr::sort(Level::one()),
            Expr::bvar(0).unwrap(),
            false,
        ));
        let context = || {
            let mut context = Context::new(&env, Budget::DEFAULT);
            context.txn.lctx.add_param(
                FVarId(n("outer")),
                n("outer"),
                Expr::const_(n("Nat"), vec![]),
                BinderInfo::Default,
            );
            context
        };
        let mut complete = context();
        let saved = complete.txn.lctx.clone();
        assert!(complete.codegen_type_former(&expr).unwrap());
        let spent = complete.txn.budget.heartbeats_consumed;
        assert!(
            spent > 5,
            "the dependent telescope must actually be visited"
        );
        for allowed in 1..spent {
            let mut limited = context();
            limited.txn.budget.max_heartbeats = allowed;
            assert!(
                limited.codegen_type_former(&expr).is_err(),
                "bound {allowed}"
            );
            assert_eq!(limited.txn.lctx, saved, "bound {allowed}");
            assert_eq!(limited.txn.env, env, "bound {allowed}");
        }
        assert_eq!(complete.txn.lctx, saved);
    }
}
