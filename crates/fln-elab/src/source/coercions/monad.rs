//! Insert registered `MonadLiftT` actions without evaluating or duplicating them.
//!
//! This is the direct `liftM` branch of the pin's `coerceMonadLift?`
//! (`Lean/Meta/Coe.lean`). It does not require either constructor to have a
//! `Monad` instance. Mapping a coercion over the result of an action is a
//! separate operation and is not guessed here.
use super::*;

impl Context {
    /// Apply every argument explicitly, inferring universes from the admitted
    /// declaration's actual telescope rather than assuming a universe order.
    fn lift_application(
        &mut self,
        name: &str,
        arguments: impl IntoIterator<Item = Expr>,
    ) -> Result<Option<Typed>, NatDefinitionElabError> {
        let name = Name::from_components(name.split('.'));
        if !self.txn.env.contains(&name) {
            return Ok(None);
        }
        let mut result = self.constant(&name)?;
        for argument in arguments {
            self.tick()?;
            let signature = self.whnf(&result.type_)?;
            let ExprNode::ForallE {
                binder_type, body, ..
            } = signature.node()
            else {
                return Ok(None);
            };
            let Some(actual) = self.known_type(&argument)? else {
                return Ok(None);
            };
            if !self.coercion_eq(&actual, binder_type)? {
                return Ok(None);
            }
            result.type_ = self.substitute(body, &argument)?;
            result.value = Expr::app(result.value, argument);
        }
        result.value = self.instantiate(&result.value)?;
        result.type_ = self.instantiate(&result.type_)?;
        Ok(Some(result))
    }

    /// The speculative implementation. The caller owns rollback, including
    /// assignments made while inferring the lifted action's element type.
    fn monad_lift(
        &mut self,
        term: &Typed,
        expected: &Expr,
    ) -> Result<Option<Typed>, NatDefinitionElabError> {
        self.tick()?;
        if !self
            .txn
            .options
            .get_bool(&Name::from_components(["autoLift"]), true)
            || !self.has_coercion_class("MonadLiftT")?
        {
            return Ok(None);
        }
        let actual = self.whnf(&term.type_)?;
        let target = self.whnf(expected)?;
        let (
            ExprNode::App {
                f: from,
                a: element,
            },
            ExprNode::App { f: to, .. },
        ) = (actual.node(), target.node())
        else {
            return Ok(None);
        };
        // A lift can infer the result element, but must not select an unknown
        // source or destination constructor by instance search.
        if from.has_expr_mvar() || to.has_expr_mvar() || self.defeq_guarded(from, to)? {
            return Ok(None);
        }
        let Some(class) = self.lift_application("MonadLiftT", [from.clone(), to.clone()])? else {
            return Ok(None);
        };
        let Some(instance) = self.coercion_instance(class.value)? else {
            return Ok(None);
        };
        let Some(result) = self.lift_application(
            "liftM",
            [
                from.clone(),
                to.clone(),
                instance,
                element.clone(),
                term.value.clone(),
            ],
        )?
        else {
            return Ok(None);
        };
        if !self.coercion_eq(&result.type_, expected)? {
            return Ok(None);
        }
        Ok(Some(Typed {
            value: self.instantiate(&result.value)?,
            type_: self.instantiate(&result.type_)?,
        }))
    }

    /// Failed search or type matching never leaks dictionaries, universes,
    /// pending equations or fresh identities into another coercion attempt.
    /// Heartbeats are retained even when the speculative state is discarded.
    pub(super) fn try_monad_lift(
        &mut self,
        term: &Typed,
        expected: &Expr,
    ) -> Result<Option<Typed>, NatDefinitionElabError> {
        let mut trial = self.clone();
        let result = trial.monad_lift(term, expected);
        self.txn.budget.heartbeats_consumed = trial.txn.budget.heartbeats_consumed;
        match result {
            Ok(Some(result)) => {
                *self = trial;
                Ok(Some(result))
            }
            Ok(None) => Ok(None),
            Err(error) if nonmatch(&error) => Ok(None),
            Err(error) => Err(error),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::instances::register_class;
    use crate::records::{RecordBudget, RecordSpec, record_declarations};
    use fln_core::options::DataValue;
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
    fn app(head: Expr, args: impl IntoIterator<Item = Expr>) -> Expr {
        args.into_iter().fold(head, Expr::app)
    }
    fn universe() -> Expr {
        Expr::sort(Level::one())
    }
    fn constructor_type() -> Expr {
        Expr::forall_e(n("a"), universe(), universe(), BinderInfo::Default)
    }
    fn parameter(
        locals: &mut LocalContext,
        name: &str,
        type_: Expr,
        style: BinderInfo,
    ) -> LocalDecl {
        locals
            .add_param(FVarId(n(name)), n(name), type_, style)
            .clone()
    }
    fn fv(local: &LocalDecl) -> Expr {
        Expr::fvar(local.id.clone())
    }
    fn close(locals: &[LocalDecl], mut body: Expr, lambda: bool) -> Expr {
        for local in locals.iter().rev() {
            body = body.abstract_fvar(&local.id, 0).unwrap();
            body = if lambda {
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
            };
        }
        body
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
        let mut locals = LocalContext::new();
        let mut from = parameter(&mut locals, "m", constructor_type(), BinderInfo::Default);
        let mut to = parameter(&mut locals, "n", constructor_type(), BinderInfo::Default);
        let element = parameter(&mut locals, "a", universe(), BinderInfo::Implicit);
        let action = parameter(
            &mut locals,
            "x",
            Expr::app(fv(&from), fv(&element)),
            BinderInfo::Default,
        );
        let result = Expr::app(fv(&to), fv(&element));
        let field = parameter(
            &mut locals,
            "monadLift",
            close(&[element.clone(), action.clone()], result.clone(), false),
            BinderInfo::Default,
        );
        for declaration in record_declarations(
            &RecordSpec {
                name: n("MonadLiftT"),
                level_params: vec![],
                parameters: vec![from.clone(), to.clone()],
                fields: vec![field],
                result_level: Level::one().succ().unwrap(),
                is_class: true,
            },
            RecordBudget::default(),
        )
        .unwrap()
        {
            env = publish(&env, declaration);
        }
        env = register_class(&env, &n("MonadLiftT")).unwrap();
        from.binder_info = BinderInfo::Implicit;
        to.binder_info = BinderInfo::Implicit;
        let instance = parameter(
            &mut locals,
            "inst",
            app(c("MonadLiftT"), [fv(&from), fv(&to)]),
            BinderInfo::InstImplicit,
        );
        let body = app(
            c("MonadLiftT.monadLift"),
            [fv(&from), fv(&to), fv(&instance), fv(&element), fv(&action)],
        );
        let parameters = [from, to, instance, element, action];
        publish(
            &env,
            Declaration::Defn(DefinitionVal {
                base: ConstantVal {
                    name: n("liftM"),
                    level_params: vec![],
                    type_: close(&parameters, result, false),
                },
                value: close(&parameters, body, true),
                hints: ReducibilityHints::Abbrev,
                safety: DefinitionSafety::Safe,
                all: vec![n("liftM")],
            }),
        )
    }
    fn source_value(source: &str) -> Expr {
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
    fn has_lift(value: &Expr) -> bool {
        let mut work = vec![value];
        while let Some(expr) = work.pop() {
            match expr.node() {
                ExprNode::Const { name, .. } if name == &n("liftM") => return true,
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
    fn context(with_instance: bool) -> (Context, Typed, Expr) {
        let mut context = Context::new(&environment(), budget());
        let from = parameter(
            &mut context.txn.lctx,
            "m",
            constructor_type(),
            BinderInfo::Default,
        );
        let to = parameter(
            &mut context.txn.lctx,
            "n",
            constructor_type(),
            BinderInfo::Default,
        );
        if with_instance {
            parameter(
                &mut context.txn.lctx,
                "inst",
                app(c("MonadLiftT"), [fv(&from), fv(&to)]),
                BinderInfo::InstImplicit,
            );
        }
        let type_ = Expr::app(fv(&from), c("Nat"));
        let action = parameter(
            &mut context.txn.lctx,
            "x",
            type_.clone(),
            BinderInfo::Default,
        );
        (
            context,
            Typed {
                value: fv(&action),
                type_,
            },
            Expr::app(fv(&to), c("Nat")),
        )
    }

    #[test]
    fn a_registered_lift_accepts_an_action_without_monad_instances() {
        assert!(has_lift(&source_value(
            "def lifted (m n : Type -> Type) [inst : MonadLiftT m n] (x : m Nat) : n Nat := x"
        )));
    }

    #[test]
    fn lifting_also_works_at_explicit_function_arguments() {
        assert!(has_lift(&source_value(
            "def lifted (m n : Type -> Type) [inst : MonadLiftT m n] (use : n Nat -> Nat) (x : m Nat) : Nat := use x"
        )));
    }

    #[test]
    fn an_action_already_in_the_expected_monad_is_not_lifted() {
        assert!(!has_lift(&source_value(
            "def retained (m : Type -> Type) [inst : MonadLiftT m m] (x : m Nat) : m Nat := x"
        )));
    }

    #[test]
    fn missing_reversed_and_wrong_element_lifts_are_not_admitted() {
        let env = environment();
        for source in [
            "def bad (m n : Type -> Type) (x : m Nat) : n Nat := x",
            "def bad (m n : Type -> Type) [inst : MonadLiftT n m] (x : m Nat) : n Nat := x",
            "def bad (m n : Type -> Type) [inst : MonadLiftT m n] (x : m Nat) : n (Nat -> Nat) := x",
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
    fn auto_lift_false_disables_insertion() {
        let (mut context, action, expected) = context(true);
        context
            .txn
            .options
            .insert(n("autoLift"), DataValue::OfBool(false));
        assert!(
            context
                .try_monad_lift(&action, &expected)
                .unwrap()
                .is_none()
        );
    }

    #[test]
    fn a_failed_lift_rolls_back_semantics_but_not_work() {
        let (mut context, action, expected) = context(false);
        let before = context.txn.clone();
        let next = context.next;
        assert!(
            context
                .try_monad_lift(&action, &expected)
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
    fn exhaustion_is_not_reported_as_no_instance() {
        let (mut context, action, expected) = context(true);
        context.txn.budget.max_heartbeats = 1;
        context.txn.budget.heartbeats_consumed = 1;
        assert!(matches!(
            context.try_monad_lift(&action, &expected),
            Err(NatDefinitionElabError::Inference(
                SourceInferenceError::ResourceLimit
            ))
        ));
    }
}
