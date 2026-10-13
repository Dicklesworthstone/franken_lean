//! Expected-function coercions share the ordinary `CoeFun` search used when an
//! object is called. A failed shape or codomain check must not prevent a later
//! `CoeT` path, nor leave its output metavariable assigned in that attempt.
use super::*;

impl Context {
    pub(super) fn try_expected_function(
        &mut self,
        term: &Typed,
        expected: &Expr,
    ) -> Result<Option<Typed>, NatDefinitionElabError> {
        if !self.has_coercion_class("CoeFun")? {
            return Ok(None);
        }
        let mut trial = self.clone();
        let result = (|| {
            let expected_head = trial.whnf(expected)?;
            if !matches!(expected_head.node(), ExprNode::ForallE { .. }) {
                return Ok(None);
            }
            let Some(candidate) = trial.coerce_shape(term, true)? else {
                return Ok(None);
            };
            if !trial.coercion_eq(&candidate.type_, expected)? {
                return Ok(None);
            }
            Ok(Some(Typed {
                value: trial.instantiate(&candidate.value)?,
                type_: trial.instantiate(&candidate.type_)?,
            }))
        })();
        self.txn.budget.heartbeats_consumed = trial.txn.budget.heartbeats_consumed;
        match result {
            Ok(Some(candidate)) => {
                *self = trial;
                Ok(Some(candidate))
            }
            Ok(None) => Ok(None),
            Err(error) if nonmatch(&error) => Ok(None),
            Err(error) => Err(error),
        }
    }
}

#[cfg(test)]
mod tests {
    mod inference;
    use super::*;
    use crate::instances::register_class;
    use crate::records::{RecordBudget, RecordSpec, record_declarations};
    use fln_env::environment::{DeclarationBudget, DeclarationCommitted};
    use fln_env::pmap::CollisionBudget;
    use fln_kernel::capability::{Published, admit};
    use fln_kernel::council::{Council, CouncilOutcome, convene};

    fn n(text: &str) -> Name {
        Name::from_components(text.split('.'))
    }
    fn c(text: &str) -> Expr {
        Expr::const_(n(text), vec![])
    }
    fn arrow(domain: Expr, range: Expr) -> Expr {
        // Test helpers use closed types here, so there is no binder to lift.
        Expr::forall_e(n("x"), domain, range, BinderInfo::Default)
    }
    fn fv(local: &LocalDecl) -> Expr {
        Expr::fvar(local.id.clone())
    }
    fn local(name: &str, type_: Expr, style: BinderInfo) -> LocalDecl {
        LocalDecl {
            id: FVarId(n(name)),
            user_name: n(name),
            type_,
            value: None,
            binder_info: style,
            index: 0,
        }
    }
    fn close(local: &LocalDecl, body: Expr, lambda: bool) -> Expr {
        let body = body.abstract_fvar(&local.id, 0).unwrap();
        if lambda {
            Expr::lam(
                local.user_name.clone(),
                local.type_.clone(),
                body,
                local.binder_info,
            )
        } else {
            Expr::forall_e(
                local.user_name.clone(),
                local.type_.clone(),
                body,
                local.binder_info,
            )
        }
    }
    fn budget() -> Budget {
        Budget::for_stack_bytes(2 * 1024 * 1024)
    }
    fn publish(env: &Environment, declaration: Declaration) -> Environment {
        let Outcome::Complete(admitted) = admit(env, declaration, budget()) else {
            panic!("fixture admission must answer");
        };
        let CouncilOutcome::Agreed(checked) = convene(&Council::nobody_was_asked(), admitted)
        else {
            panic!("fixture must be kernel accepted");
        };
        match checked.publish(
            DeclarationBudget::default(),
            CollisionBudget::default(),
            None,
        ) {
            Outcome::Complete(Published::Committed(DeclarationCommitted::Published(result))) => {
                result.environment
            }
            Outcome::Complete(Published::BlockCommitted(result)) => result.environment,
            other => panic!("fixture publication failed: {other:?}"),
        }
    }
    fn environment() -> Environment {
        let mut env = crate::seed::bootstrap_nat_environment(budget()).unwrap();
        env = publish(&env, crate::seed::out_param_seed_declaration());
        let u = Level::param(n("u"));
        let v = Level::param(n("v"));
        let a = local("A", Expr::sort(u.clone()), BinderInfo::Default);
        let x = local("x", fv(&a), BinderInfo::Default);
        let output_type = close(&x, Expr::sort(v.clone()), false);
        let output_level = Level::max(u.clone(), v.clone().succ().unwrap()).unwrap();
        let b = local(
            "B",
            Expr::app(Expr::const_(n("outParam"), vec![output_level]), output_type),
            BinderInfo::Default,
        );
        let coe = local(
            "coe",
            close(&x, Expr::app(fv(&b), fv(&x)), false),
            BinderInfo::Default,
        );
        let result_level =
            Level::max(Level::one(), Level::max(u.clone(), v.clone()).unwrap()).unwrap();
        for declaration in record_declarations(
            &RecordSpec {
                name: n("CoeFun"),
                level_params: vec![n("u"), n("v")],
                parameters: vec![a.clone(), b],
                fields: vec![coe],
                result_level: result_level.clone(),
                is_class: true,
            },
            RecordBudget::default(),
        )
        .unwrap()
        {
            env = publish(&env, declaration);
        }
        env = register_class(&env, &n("CoeFun")).unwrap();
        let b = local("B", Expr::sort(v), BinderInfo::Default);
        let coe = local("coe", fv(&b), BinderInfo::Default);
        for declaration in record_declarations(
            &RecordSpec {
                name: n("CoeT"),
                level_params: vec![n("u"), n("v")],
                parameters: vec![a, x, b],
                fields: vec![coe],
                result_level,
                is_class: true,
            },
            RecordBudget::default(),
        )
        .unwrap()
        {
            env = publish(&env, declaration);
        }
        register_class(&env, &n("CoeT")).unwrap()
    }
    fn accepted(source: &str) -> Expr {
        let checked = crate::check_definition_source(source.as_bytes(), &environment(), budget())
            .unwrap_or_else(|error| panic!("{source}: {error:?}"));
        assert!(
            matches!(checked.outcome, Outcome::Complete(Verdict::Accepted { .. })),
            "{source}: {:?}",
            checked.outcome
        );
        let Declaration::Defn(declaration) = checked.declaration else {
            panic!("expected a definition");
        };
        assert!(!declaration.value.has_expr_mvar());
        assert!(!declaration.value.has_level_mvar());
        assert!(!declaration.value.has_fvar());
        assert!(!declaration.value.has_loose_bvars());
        declaration.value
    }
    fn contains(value: &Expr, name: &str) -> bool {
        let mut work = vec![value];
        while let Some(expr) = work.pop() {
            match expr.node() {
                ExprNode::Const { name: actual, .. } if actual == &n(name) => return true,
                ExprNode::App { f, a } => work.extend([f, a]),
                ExprNode::Lam {
                    binder_type, body, ..
                }
                | ExprNode::ForallE {
                    binder_type, body, ..
                } => work.extend([binder_type, body]),
                ExprNode::LetE {
                    type_, value, body, ..
                } => work.extend([type_, value, body]),
                ExprNode::MData { expr, .. } => work.push(expr),
                _ => {}
            }
        }
        false
    }

    #[test]
    fn a_bundled_function_can_be_returned_at_an_expected_arrow() {
        let value = accepted(
            "def asFn (W : Type) [inst : CoeFun W (fun _ => Nat -> Nat)] (w : W) : Nat -> Nat := w",
        );
        assert!(contains(&value, "CoeFun.coe"));
    }

    #[test]
    fn a_bundled_function_can_be_passed_to_a_higher_order_function() {
        let value = accepted(
            "def pass (W : Type) [inst : CoeFun W (fun _ => Nat -> Nat)] (w : W) (use : (Nat -> Nat) -> Nat) : Nat := use w",
        );
        assert!(contains(&value, "CoeFun.coe"));
    }

    #[test]
    fn ordinary_functions_and_direct_function_position_remain_valid() {
        let value = accepted("def keep (f : Nat -> Nat) : Nat -> Nat := f");
        assert!(!contains(&value, "CoeFun.coe"));
        let value = accepted(
            "def call (W : Type) [inst : CoeFun W (fun _ => Nat -> Nat)] (w : W) (x : Nat) : Nat := w x",
        );
        assert!(contains(&value, "CoeFun.coe"));
    }

    #[test]
    fn a_wrong_function_shape_does_not_block_a_valid_value_coercion() {
        let value = accepted(
            "def fallback (W : Type) [fn : CoeFun W (fun _ => Nat -> Nat -> Nat)] (w : W) [val : CoeT W w (Nat -> Nat)] : Nat -> Nat := w",
        );
        assert!(contains(&value, "CoeT.coe"));
        assert!(!contains(&value, "CoeFun.coe"));
    }

    #[test]
    fn missing_instances_and_wrong_function_ranges_cannot_be_admitted() {
        let env = environment();
        for source in [
            "def bad (W : Type) (w : W) : Nat -> Nat := w",
            "def bad (W : Type) [inst : CoeFun W (fun _ => Nat -> Nat)] (w : W) : Nat -> Nat -> Nat := w",
            "def bad (W : Type) [inst : CoeFun W (fun _ => Nat)] (w : W) : Nat -> Nat := w",
        ] {
            if let Ok(checked) = crate::check_definition_source(source.as_bytes(), &env, budget()) {
                assert!(
                    !matches!(checked.outcome, Outcome::Complete(Verdict::Accepted { .. })),
                    "{source}"
                );
            }
        }
    }

    #[test]
    fn a_failed_function_probe_preserves_semantics_and_charges_work() {
        let mut context = Context::new(&environment(), budget());
        let id = FVarId(n("w"));
        context
            .txn
            .lctx
            .add_param(id.clone(), n("w"), c("Nat"), BinderInfo::Default);
        let term = Typed {
            value: Expr::fvar(id),
            type_: c("Nat"),
        };
        let before = context.txn.clone();
        let next = context.next;
        assert!(
            context
                .try_expected_function(&term, &arrow(c("Nat"), c("Nat")))
                .unwrap()
                .is_none()
        );
        assert!(context.txn.budget.heartbeats_consumed > before.budget.heartbeats_consumed);
        let mut after = context.txn.clone();
        after.budget = before.budget.clone();
        assert_eq!(after, before);
        assert_eq!(context.next, next);
        assert!(context.instance_goals.is_empty());
    }

    #[test]
    fn function_coercion_exhaustion_stays_a_resource_error() {
        let mut context = Context::new(&environment(), budget());
        let term = Typed {
            value: c("Nat"),
            type_: Expr::sort(Level::one()),
        };
        context.txn.budget.max_heartbeats = 1;
        context.txn.budget.heartbeats_consumed = 1;
        assert!(matches!(
            context.try_expected_function(&term, &arrow(c("Nat"), c("Nat"))),
            Err(NatDefinitionElabError::Inference(
                SourceInferenceError::ResourceLimit
            ))
        ));
    }
}
