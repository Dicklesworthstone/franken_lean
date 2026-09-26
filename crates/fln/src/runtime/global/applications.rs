//! Each returned-function application completes before the next argument.
//! A flat callback may underapply here; its existing suffix interface still
//! determines the representation. No guessed arity or interface cast is used.
use super::*;

struct Stage {
    argument: Binder,
    result_type: Expr,
}

impl Preparation<'_> {
    pub(super) fn apply_producer(
        &mut self,
        value: Expr,
        type_: Expr,
        args: &[Expr],
        outer_depth: usize,
    ) -> Result<Option<Expr>, IngressError> {
        let mut stages = Vec::new();
        let mut result_type = type_.clone();
        let mut depth = outer_depth
            .checked_add(1)
            .ok_or_else(|| unsupported("global application depth"))?;
        self.producer_depth(depth)?;
        for argument in args {
            self.tick()?;
            let normal = self.type_head(&result_type)?;
            let ExprNode::ForallE {
                binder_name,
                binder_type,
                body,
                ..
            } = normal.node()
            else {
                return Ok(None);
            };
            if binder_type.has_loose_bvars() || body.has_loose_bvars() {
                return Ok(None);
            }
            // Every preceding stage introduced its argument and its result.
            // Lift only the caller's argument, not the already scoped producer.
            let offset = self.producer_depth(depth)?;
            depth = depth
                .checked_add(2)
                .ok_or_else(|| unsupported("global application depth"))?;
            self.producer_depth(depth)?;
            reserve(&mut stages, self.limits.max_application_args)?;
            stages.push(Stage {
                argument: Binder {
                    name: binder_name.clone(),
                    domain: binder_type.clone(),
                    value: self.lift(argument, offset)?,
                },
                result_type: body.clone(),
            });
            result_type = body.clone();
        }
        let mut applied = variable(0)?;
        for stage in stages.into_iter().rev() {
            self.tick()?;
            // The previous function is immediately outside this argument's
            // binder. Binding its result now prevents the next initializer
            // from crossing a saturated, possibly effectful callback stage.
            applied = Expr::let_e(
                Name::anonymous(),
                stage.result_type,
                Expr::app(variable(1)?, variable(0)?),
                applied,
                false,
            );
            applied = Expr::let_e(
                stage.argument.name,
                stage.argument.domain,
                stage.argument.value,
                applied,
                false,
            );
        }
        let value = self.annotate_execution_value(value, type_.clone())?;
        Ok(Some(Expr::let_e(
            Name::anonymous(),
            type_,
            value,
            applied,
            false,
        )))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ty() -> Expr {
        Expr::const_(name("Nat"), vec![])
    }
    fn pi(body: Expr) -> Expr {
        Expr::forall_e(Name::anonymous(), ty(), body, BinderInfo::Default)
    }
    fn b(index: usize) -> Expr {
        variable(index).unwrap()
    }
    fn call(label: &str, value: Expr) -> Expr {
        Expr::app(Expr::const_(name(label), vec![]), value)
    }

    #[test]
    fn each_application_is_bound_before_the_next_argument_initializer() {
        let environment = Environment::new();
        let producer = call("producer", b(0));
        let result = Preparation::new(&environment, IngressLimits::default())
            .apply_producer(
                producer,
                pi(pi(ty())),
                &[call("first", b(0)), call("last", b(1))],
                2,
            )
            .unwrap()
            .unwrap();
        let ExprNode::LetE { body, .. } = result.node() else {
            panic!("producer binding");
        };
        let ExprNode::LetE { value, body, .. } = body.node() else {
            panic!("first argument");
        };
        assert_eq!(*value, call("first", b(3)));
        let ExprNode::LetE {
            type_, value, body, ..
        } = body.node()
        else {
            panic!("first application precedes second argument");
        };
        assert_eq!(*type_, pi(ty()));
        assert_eq!(*value, Expr::app(b(1), b(0)));
        let ExprNode::LetE { value, body, .. } = body.node() else {
            panic!("second argument");
        };
        assert_eq!(*value, call("last", b(6)));
        let ExprNode::LetE {
            type_, value, body, ..
        } = body.node()
        else {
            panic!("second application");
        };
        assert_eq!(*type_, ty());
        assert_eq!(*value, Expr::app(b(1), b(0)));
        assert_eq!(*body, b(0));
    }

    #[test]
    fn arguments_are_lifted_capture_avoidantly_not_substituted_or_duplicated() {
        let environment = Environment::new();
        let callback_type = pi(ty());
        let callback = Expr::lam(
            name("x"),
            ty(),
            Expr::app(call("Nat.add", b(1)), b(0)),
            BinderInfo::Default,
        );
        let type_ = Expr::forall_e(
            Name::anonymous(),
            callback_type.clone(),
            ty(),
            BinderInfo::Default,
        );
        let result = Preparation::new(&environment, IngressLimits::default())
            .apply_producer(call("producer", b(0)), type_, &[callback], 2)
            .unwrap()
            .unwrap();
        let ExprNode::LetE { body, .. } = result.node() else {
            panic!("producer");
        };
        let ExprNode::LetE { type_, value, .. } = body.node() else {
            panic!("typed callback argument");
        };
        assert_eq!(*type_, callback_type);
        assert_eq!(
            *value,
            Expr::lam(
                name("x"),
                ty(),
                Expr::app(call("Nat.add", b(4)), b(0)),
                BinderInfo::Default,
            )
        );
    }

    #[test]
    fn scalar_overapplication_is_refused_instead_of_cast_to_a_function() {
        let environment = Environment::new();
        assert!(
            Preparation::new(&environment, IngressLimits::default())
                .apply_producer(call("producer", b(0)), pi(ty()), &[b(0), b(0)], 0)
                .unwrap()
                .is_none()
        );
    }

    #[test]
    fn combined_context_counts_intermediate_results_before_allocating_their_spine() {
        let environment = Environment::new();
        let limits = IngressLimits {
            max_context_depth: 6,
            ..IngressLimits::default()
        };
        assert!(matches!(
            Preparation::new(&environment, limits)
                .apply_producer(call("producer", b(0)), pi(pi(ty())), &[b(0), b(0)], 2),
            Err(IngressError::ResourceLimit {
                resource: IngressResource::ContextDepth,
                limit: 6,
                observed: 7,
            })
        ));
    }
}
