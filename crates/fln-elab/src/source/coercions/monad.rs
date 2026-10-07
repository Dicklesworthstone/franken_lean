//! Insert monadic lifts and result coercions without executing an action.
//!
//! The three branches of the pin's `coerceMonadLift?` (Lean/Meta/Coe.lean):
//! `coeM` within one monad, direct `liftM`, then `liftCoeM` when both a lift
//! and a result coercion are needed. These are applications of admitted
//! library definitions, not new runtime primitives or proof rules.
use super::*;

impl Context {
    /// Apply every argument explicitly, inferring universes from the admitted
    /// declaration's actual telescope rather than assuming a universe order.
    fn lift_application(
        &mut self,
        name: &str,
        arguments: impl IntoIterator<Item = Expr>,
    ) -> Result<Option<Typed>, NatDefinitionElabError> {
        self.monadic_application(name, arguments.into_iter().map(Some))
    }

    /// `None` asks ordinary instance search for this exact instance binder.
    /// In particular, the result dictionary is `forall a, CoeT alpha a beta`:
    /// finding a coercion for one specific value is not sufficient. Never
    /// invent a value for a non-instance argument or silently leave a hole.
    fn monadic_application(
        &mut self,
        name: &str,
        arguments: impl IntoIterator<Item = Option<Expr>>,
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
                binder_type,
                body,
                binder_info,
                ..
            } = signature.node()
            else {
                return Ok(None);
            };
            let argument = match argument {
                Some(argument) => argument,
                None if *binder_info == BinderInfo::InstImplicit => {
                    let target = self.instantiate(binder_type)?;
                    let Some(instance) = self.coercion_instance(target)? else {
                        return Ok(None);
                    };
                    instance
                }
                None => return Ok(None),
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

    fn monad_dictionary(
        &mut self,
        constructor: &Expr,
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        if !self.has_coercion_class("Monad")? {
            return Ok(None);
        }
        let Some(target) = self.lift_application("Monad", [constructor.clone()])? else {
            return Ok(None);
        };
        self.coercion_instance(target.value)
    }

    /// Expansion is selective: keep user functions folded, and unfold only
    /// the coercion helpers and projections tagged in the pin. Re-infer after
    /// expansion rather than asserting that the requested target was produced.
    fn finish_monadic_coercion(
        &mut self,
        result: Typed,
        expected: &Expr,
    ) -> Result<Option<Typed>, NatDefinitionElabError> {
        let value = self.instantiate(&result.value)?;
        let value = self.expand_coercions(&value)?;
        let Some(type_) = self.known_type(&value)? else {
            return Ok(None);
        };
        if !self.coercion_eq(&type_, expected)? {
            return Ok(None);
        }
        Ok(Some(Typed {
            value: self.instantiate(&value)?,
            type_: self.instantiate(&type_)?,
        }))
    }

    /// The speculative implementation. The caller owns rollback, including
    /// assignments made while inferring the lifted action's element type.
    fn monad_lift(
        &mut self,
        term: &Typed,
        expected: &Expr,
    ) -> Result<Option<Typed>, NatDefinitionElabError> {
        self.tick()?;
        // Recover the value's own type: application elaboration may already
        // have normalized Typed.type_ to a function. Like the pin's
        // `isTypeApp?`, reduce aliases, not ordinary monad definitions such
        // as function-backed state/reader transformers.
        let Some(actual) = self.known_type(&term.value)? else {
            return Ok(None);
        };
        let actual =
            self.whnf_with_transparency(&actual, UnificationTransparency::Abbreviations, true)?;
        let target =
            self.whnf_with_transparency(expected, UnificationTransparency::Abbreviations, true)?;
        let (
            ExprNode::App {
                f: from,
                a: element,
            },
            ExprNode::App {
                f: to,
                a: expected_element,
            },
        ) = (actual.node(), target.node())
        else {
            return Ok(None);
        };
        // Instance search must not choose an unknown monad constructor.
        if from.has_expr_mvar() || to.has_expr_mvar() {
            return Ok(None);
        }
        if self.defeq_guarded(from, to)? {
            // `autoLift` controls changing monads, not coercing a result in
            // the same monad. No MonadLiftT dictionary is needed in this branch.
            let Some(monad) = self.monad_dictionary(to)? else {
                return Ok(None);
            };
            let Some(result) = self.monadic_application(
                "Lean.Internal.coeM",
                [
                    Some(from.clone()),
                    Some(element.clone()),
                    Some(expected_element.clone()),
                    None,
                    Some(monad),
                    Some(term.value.clone()),
                ],
            )?
            else {
                return Ok(None);
            };
            return self.finish_monadic_coercion(result, expected);
        }
        if !self
            .txn
            .options
            .get_bool(&Name::from_components(["autoLift"]), true)
            || !self.has_coercion_class("MonadLiftT")?
        {
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
                instance.clone(),
                element.clone(),
                term.value.clone(),
            ],
        )?
        else {
            return Ok(None);
        };
        // A failed direct-result probe must not constrain the fallback's
        // output type. The successful lift dictionary remains available.
        if self.defeq_guarded(&result.type_, expected)? {
            return Ok(Some(Typed {
                value: self.instantiate(&result.value)?,
                type_: self.instantiate(&result.type_)?,
            }));
        }
        // Only the destination must be a Monad. The source merely needs its
        // registered lift; the action occurs once in the admitted helper body.
        let Some(monad) = self.monad_dictionary(to)? else {
            return Ok(None);
        };
        let Some(result) = self.monadic_application(
            "Lean.Internal.liftCoeM",
            [
                Some(from.clone()),
                Some(to.clone()),
                Some(element.clone()),
                Some(expected_element.clone()),
                Some(instance),
                None,
                Some(monad),
                Some(term.value.clone()),
            ],
        )?
        else {
            return Ok(None);
        };
        self.finish_monadic_coercion(result, expected)
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
    mod constructors;
    mod inference;
    mod results;

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
