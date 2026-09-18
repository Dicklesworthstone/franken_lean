//! Source quotient computation shares the ordinary heap continuation machine.
//! Only admitted quotient tags enable computation, never a matching spelling.
//! Reduction does not discharge the original expression's typing obligations:
//! respectfulness and induction proofs still enter ordinary source/K1 checking.
use super::*;
use fln_env::constants::QuotKind;

impl Context {
    /// A saturated primitive's major position, in forward application order.
    /// Check the entire registered quartet, not merely a familiar-looking head.
    pub(super) fn source_quotient_major(
        &mut self,
        head: &Expr,
        arguments: usize,
    ) -> Result<Option<usize>, NatDefinitionElabError> {
        let ExprNode::Const { name, levels } = head.node() else {
            return Ok(None);
        };
        let root = Name::from_components(["Quot"]);
        let (major, level_count) = if name == &Name::str(root.clone(), "lift") {
            (5, 2)
        } else if name == &Name::str(root.clone(), "ind") {
            (4, 1)
        } else {
            return Ok(None);
        };
        if arguments <= major || levels.len() != level_count {
            return Ok(None);
        }
        let u = Name::from_components(["u"]);
        let v = Name::from_components(["v"]);
        for (expected, kind, count) in [
            (root.clone(), QuotKind::Type, 1),
            (Name::str(root.clone(), "mk"), QuotKind::Ctor, 1),
            (Name::str(root.clone(), "lift"), QuotKind::Lift, 2),
            (Name::str(root, "ind"), QuotKind::Ind, 1),
        ] {
            self.tick()?;
            let Some(ConstantInfo::Quot(primitive)) = self.txn.env.find(&expected) else {
                return Ok(None);
            };
            let parameters = &primitive.base.level_params;
            // Quotient initialization at the pin requires these parameter names
            // and this order. The type bodies were checked at admission; do not
            // clone or rewalk them on every reduction.
            if primitive.base.name != expected
                || primitive.kind != kind
                || parameters.len() != count
                || parameters.first() != Some(&u)
                || (count == 2 && parameters.get(1) != Some(&v))
            {
                return Ok(None);
            }
        }
        Ok(Some(major))
    }

    /// `Quot.lift f h (Quot.mk r a)` and `Quot.ind h (Quot.mk r a)`
    /// compute to `f a` and `h a`. Both branches occupy forward argument 3;
    /// the representative occupies forward argument 2 of the constructor.
    /// Every slice here is in the reducer's reverse-application order.
    pub(super) fn source_quotient_step(
        &mut self,
        eliminator: &Expr,
        arguments: &[Expr],
        major_head: &Expr,
        major_arguments: &[Expr],
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        self.tick()?;
        if major_arguments.len() != 3 {
            return Ok(None);
        }
        let eliminator = self.instantiate(eliminator)?;
        let constructor = self.instantiate(major_head)?;
        let ExprNode::Const { levels, .. } = eliminator.node() else {
            return Ok(None);
        };
        let ExprNode::Const {
            name,
            levels: constructor_levels,
        } = constructor.node()
        else {
            return Ok(None);
        };
        if name != &Name::from_components(["Quot", "mk"]) || constructor_levels.len() != 1 {
            return Ok(None);
        }
        let Some(level) = levels.first() else {
            return Ok(None);
        };
        // Do not solve universe holes just to unlock computation. A later
        // equation can assign them and the ordinary retry loop will revisit it.
        // Structural equality here is sufficient, not a negative conversion verdict.
        if level != &constructor_levels[0] {
            return Ok(None);
        }
        let Some(branch_position) = arguments.len().checked_sub(4) else {
            return Ok(None);
        };
        let Some(branch) = arguments.get(branch_position) else {
            return Ok(None);
        };
        self.tick()?;
        Ok(Some(Expr::app(branch.clone(), major_arguments[0].clone())))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use fln_core::expr::NatLit;
    use fln_core::outcome::Outcome;
    use fln_env::environment::DeclarationBudget;
    use fln_env::pmap::CollisionBudget;
    use fln_kernel::capability::{Published, admit};
    use fln_kernel::council::{Council, CouncilOutcome, convene};

    fn name(text: &str) -> Name {
        Name::from_components(text.split('.'))
    }
    fn bv(index: u32) -> Expr {
        Expr::bvar(index).unwrap()
    }
    fn nat() -> Expr {
        Expr::const_(name("Nat"), vec![])
    }
    fn number(value: u64) -> Expr {
        Expr::lit(Literal::Nat(NatLit::from_u64(value)))
    }
    fn app(head: Expr, args: impl IntoIterator<Item = Expr>) -> Expr {
        args.into_iter().fold(head, Expr::app)
    }
    fn lam(domain: Expr, body: Expr) -> Expr {
        Expr::lam(Name::anonymous(), domain, body, BinderInfo::Default)
    }
    fn eq(type_: Expr, left: Expr, right: Expr) -> Expr {
        app(
            Expr::const_(name("Eq"), vec![Level::one()]),
            [type_, left, right],
        )
    }
    fn relation() -> Expr {
        lam(nat(), lam(nat(), eq(nat(), bv(1), bv(0))))
    }
    fn quotient_type() -> Expr {
        app(
            Expr::const_(name("Quot"), vec![Level::one()]),
            [nat(), relation()],
        )
    }
    fn representative(value: Expr) -> Expr {
        app(
            Expr::const_(name("Quot.mk"), vec![Level::one()]),
            [nat(), relation(), value],
        )
    }
    fn lift(major: Expr) -> Expr {
        let respects = lam(nat(), lam(nat(), lam(eq(nat(), bv(1), bv(0)), bv(0))));
        app(
            Expr::const_(name("Quot.lift"), vec![Level::one(), Level::one()]),
            [nat(), relation(), nat(), lam(nat(), bv(0)), respects, major],
        )
    }
    fn environment() -> Environment {
        let budget = Budget::for_stack_bytes(2 * 1024 * 1024);
        let mut env = crate::seed::bootstrap_nat_environment(budget).unwrap();
        for declaration in [
            crate::seed::eq_seed_declaration(),
            crate::seed::quotient_seed_declaration(),
        ] {
            let Outcome::Complete(admitted) = admit(&env, declaration, budget) else {
                panic!("admission nonanswer")
            };
            let CouncilOutcome::Agreed(checked) = convene(&Council::nobody_was_asked(), admitted)
            else {
                panic!("rejected seed")
            };
            let Outcome::Complete(Published::BlockCommitted(result)) = checked.publish(
                DeclarationBudget::default(),
                CollisionBudget::default(),
                None,
            ) else {
                panic!("publication nonanswer")
            };
            env = result.environment;
        }
        env
    }
    #[test]
    fn source_quotient_reduces_without_global_delta() {
        let mut context = Context::new(&environment(), Budget::DEFAULT);
        assert_eq!(
            context
                .whnf_with_transparency(
                    &lift(representative(number(7))),
                    UnificationTransparency::None,
                    false
                )
                .unwrap(),
            number(7)
        );
    }
    #[test]
    fn source_quotient_preserves_local_let_policy_and_noop_sharing() {
        let mut context = Context::new(&environment(), Budget::DEFAULT);
        let id = FVarId(name("q"));
        context.txn.lctx.add_let(
            id.clone(),
            id.0.clone(),
            quotient_type(),
            representative(number(7)),
        );
        let expression = lift(Expr::fvar(id));
        let blocked = context
            .whnf_with_transparency(&expression, UnificationTransparency::None, false)
            .unwrap();
        assert!(std::ptr::eq(blocked.node(), expression.node()));
        assert_eq!(
            context
                .whnf_with_transparency(&expression, UnificationTransparency::None, true)
                .unwrap(),
            number(7)
        );
    }
    #[test]
    fn source_quotient_requires_registered_primitives() {
        let mut context = Context::new(&Environment::new(), Budget::DEFAULT);
        let expression = lift(representative(number(7)));
        assert_eq!(context.whnf(&expression).unwrap(), expression);
    }
    #[test]
    fn malformed_and_neutral_quotient_majors_stay_blocked() {
        let mut context = Context::new(&environment(), Budget::DEFAULT);
        for major in [
            Expr::fvar(FVarId(name("q"))),
            app(
                Expr::const_(name("Quot.mk"), vec![Level::zero()]),
                [nat(), relation(), number(7)],
            ),
            app(
                Expr::const_(name("Quot.mk"), vec![Level::one()]),
                [nat(), relation()],
            ),
            Expr::app(representative(number(7)), number(8)),
        ] {
            let expression = lift(major);
            assert_eq!(context.whnf(&expression).unwrap(), expression);
        }
    }
    #[test]
    fn source_quotient_budget_stops_preserve_semantic_state_and_allow_recovery() {
        let env = environment();
        let expression = lift(representative(number(7)));
        let mut context = Context::new(&env, Budget::DEFAULT);
        assert_eq!(context.whnf(&expression).unwrap(), number(7));
        let spent = context.txn.budget.heartbeats_consumed;
        let mut limited = Context::new(&env, Budget::DEFAULT);
        limited.txn.budget.max_heartbeats = spent - 1;
        let before = limited.txn.clone();
        assert!(matches!(
            limited.whnf(&expression),
            Err(NatDefinitionElabError::Inference(
                SourceInferenceError::ResourceLimit
            ))
        ));
        assert_eq!(limited.txn.env, before.env);
        assert_eq!(limited.txn.mvars, before.mvars);
        assert_eq!(limited.txn.universes, before.universes);
        assert_eq!(limited.txn.constraints, before.constraints);
        assert!(limited.txn.budget.heartbeats_consumed > 0);
        assert_eq!(
            Context::new(&env, Budget::DEFAULT)
                .whnf(&expression)
                .unwrap(),
            number(7)
        );
    }
    #[test]
    fn source_quotient_majors_use_heap_continuations() {
        let env = environment();
        std::thread::Builder::new()
            .stack_size(64 * 1024)
            .spawn(move || {
                let fixed = representative(number(7));
                let proof = app(
                    Expr::const_(name("Eq.refl"), vec![Level::one()]),
                    [quotient_type(), fixed.clone()],
                );
                let respects = lam(nat(), lam(nat(), lam(eq(nat(), bv(1), bv(0)), proof)));
                let prefix = app(
                    Expr::const_(name("Quot.lift"), vec![Level::one(), Level::one()]),
                    [
                        nat(),
                        relation(),
                        quotient_type(),
                        lam(nat(), fixed.clone()),
                        respects,
                    ],
                );
                let mut major = fixed;
                for _ in 0..2_000 {
                    major = Expr::app(prefix.clone(), major);
                }
                let expression = lift(major);
                let mut context = Context::new(&env, Budget::for_stack_bytes(64 * 1024));
                assert_eq!(context.whnf(&expression).unwrap(), number(7));
            })
            .unwrap()
            .join()
            .unwrap();
    }
}
