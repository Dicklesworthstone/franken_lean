//! Bounded, untrusted reconstruction of types needed by source constraints.
//!
//! In particular, implicit type arguments can be function types, not just named
//! scalars. Opening binders on an explicit worklist lets their universe equations
//! be generated without recursive host-stack growth or a second trusted checker.

use super::*;

enum Task {
    Visit(Expr),
    Apply(Expr),
    Projection {
        structure: Name,
        index: u64,
        receiver: Expr,
    },
    BinderDomain {
        name: Name,
        domain: Expr,
        body: Expr,
        style: BinderInfo,
        lambda: bool,
    },
    BinderBody {
        name: Name,
        domain: Expr,
        id: FVarId,
        level: Level,
        style: BinderInfo,
        lambda: bool,
        saved: LocalContext,
    },
}

impl Context {
    pub(super) fn known_type(
        &mut self,
        expression: &Expr,
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        let saved = self.txn.lctx.clone();
        let result = self.reconstruct_type(expression);
        // Even a resource stop or an unsupported node must not leak the
        // temporary binder context into the surrounding source elaboration.
        self.txn.lctx = saved;
        result
    }

    fn reconstruct_type(
        &mut self,
        expression: &Expr,
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        let mut tasks = vec![Task::Visit(expression.clone())];
        let mut types = Vec::new();
        while let Some(task) = tasks.pop() {
            self.tick()?;
            match task {
                Task::Visit(expression) => {
                    let expression = self.instantiate(&expression)?;
                    match expression.node() {
                        ExprNode::MData { expr, .. } => tasks.push(Task::Visit(expr.clone())),
                        ExprNode::LetE { value, body, .. } => {
                            tasks.push(Task::Visit(self.substitute(body, value)?));
                        }
                        ExprNode::App { f, a } => {
                            tasks.push(Task::Apply(a.clone()));
                            tasks.push(Task::Visit(f.clone()));
                        }
                        ExprNode::Proj {
                            struct_name,
                            idx,
                            expr,
                        } => {
                            tasks.push(Task::Projection {
                                structure: struct_name.clone(),
                                index: *idx,
                                receiver: expr.clone(),
                            });
                            tasks.push(Task::Visit(expr.clone()));
                        }
                        ExprNode::Lam {
                            binder_name,
                            binder_type,
                            body,
                            binder_info,
                        }
                        | ExprNode::ForallE {
                            binder_name,
                            binder_type,
                            body,
                            binder_info,
                        } => {
                            tasks.push(Task::BinderDomain {
                                name: binder_name.clone(),
                                domain: binder_type.clone(),
                                body: body.clone(),
                                style: *binder_info,
                                lambda: matches!(expression.node(), ExprNode::Lam { .. }),
                            });
                            tasks.push(Task::Visit(binder_type.clone()));
                        }
                        _ => match self.leaf_type(&expression)? {
                            Some(type_) => types.push(type_),
                            None => return Ok(None),
                        },
                    }
                }
                Task::Apply(argument) => {
                    let type_ = types.pop().expect("function type precedes application");
                    let type_ = self.whnf(&type_)?;
                    let ExprNode::ForallE { body, .. } = type_.node() else {
                        return Ok(None);
                    };
                    types.push(self.substitute(body, &argument)?);
                }
                Task::Projection {
                    structure,
                    index,
                    receiver,
                } => {
                    let receiver_type = types.pop().expect("receiver type precedes projection");
                    let Some(type_) =
                        self.projection_type(&structure, index, &receiver, &receiver_type)?
                    else {
                        return Ok(None);
                    };
                    types.push(type_);
                }
                Task::BinderDomain {
                    name,
                    domain,
                    body,
                    style,
                    lambda,
                } => {
                    let type_ = types.pop().expect("domain type precedes binder opening");
                    let type_ = self.whnf(&type_)?;
                    let ExprNode::Sort { level } = type_.node() else {
                        return Ok(None);
                    };
                    let saved = self.txn.lctx.clone();
                    let id = FVarId(self.fresh_name()?);
                    self.txn
                        .lctx
                        .add_param(id.clone(), name.clone(), domain.clone(), style);
                    let opened = self.substitute(&body, &Expr::fvar(id.clone()))?;
                    tasks.push(Task::BinderBody {
                        name,
                        domain,
                        id,
                        level: level.clone(),
                        style,
                        lambda,
                        saved,
                    });
                    tasks.push(Task::Visit(opened));
                }
                Task::BinderBody {
                    name,
                    domain,
                    id,
                    level,
                    style,
                    lambda,
                    saved,
                } => {
                    let body_type = types.pop().expect("body type precedes binder closing");
                    let type_ = if lambda {
                        let body = body_type
                            .abstract_fvar(&id, 0)
                            .map_err(|_| failure(SourceInferenceError::Scope))?;
                        Expr::forall_e(name, domain, body, style)
                    } else {
                        let body_type = self.whnf(&body_type)?;
                        let ExprNode::Sort { level: body_level } = body_type.node() else {
                            return Ok(None);
                        };
                        Expr::sort(
                            Level::imax(level, body_level.clone())
                                .map_err(|_| failure(SourceInferenceError::Scope))?,
                        )
                    };
                    self.txn.lctx = saved;
                    types.push(type_);
                }
            }
        }
        if types.len() != 1 {
            return Ok(None);
        }
        Ok(types.pop())
    }

    /// Pinned `Lean/Meta/InferType.lean::inferProjType`: instantiate the admitted
    /// constructor telescope, replacing every preceding field by a projection
    /// of this same receiver. Coercion expansion and other source operations
    /// can expose these primitive projections, including dependent ones.
    /// This reconstructs a type only; ordinary declaration admission still
    /// checks the receiver and every projection.
    fn projection_type(
        &mut self,
        structure: &Name,
        index: u64,
        receiver: &Expr,
        receiver_type: &Expr,
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        use fln_env::constants::ConstantInfo;

        let receiver_type = self.whnf(receiver_type)?;
        let mut head = &receiver_type;
        let mut arguments = Vec::new();
        while let ExprNode::App { f, a } = head.node() {
            self.tick()?;
            arguments.push(a.clone());
            head = f;
        }
        let ExprNode::Const { name, levels } = head.node() else {
            return Ok(None);
        };
        if name != structure {
            return Ok(None);
        }
        let Some(ConstantInfo::Induct(family)) = self.txn.env.find(name).cloned() else {
            return Ok(None);
        };
        let arity = usize::try_from(u64::from(family.num_params) + u64::from(family.num_indices))
            .map_err(|_| failure(SourceInferenceError::ResourceLimit))?;
        if family.ctors.len() != 1
            || arguments.len() != arity
            || levels.len() != family.base.level_params.len()
        {
            return Ok(None);
        }
        let Some(ConstantInfo::Ctor(constructor)) = self.txn.env.find(&family.ctors[0]).cloned()
        else {
            return Ok(None);
        };
        if constructor.induct != *structure
            || constructor.num_params != family.num_params
            || index >= u64::from(constructor.num_fields)
            || levels.len() != constructor.base.level_params.len()
        {
            return Ok(None);
        }
        let mut telescope = self.instantiate_params(
            &constructor.base.type_,
            &constructor.base.level_params,
            levels,
        )?;
        for argument in arguments.iter().rev().take(family.num_params as usize) {
            self.tick()?;
            telescope = self.whnf(&telescope)?;
            let ExprNode::ForallE { body, .. } = telescope.node() else {
                return Ok(None);
            };
            telescope = self.substitute(body, argument)?;
        }
        for preceding in 0..index {
            self.tick()?;
            telescope = self.whnf(&telescope)?;
            let ExprNode::ForallE { body, .. } = telescope.node() else {
                return Ok(None);
            };
            telescope = self.substitute(
                body,
                &Expr::proj(structure.clone(), preceding, receiver.clone()),
            )?;
        }
        telescope = self.whnf(&telescope)?;
        let ExprNode::ForallE { binder_type, .. } = telescope.node() else {
            return Ok(None);
        };
        self.projection_domain(binder_type.clone()).map(Some)
    }

    /// `inferProjType` consumes only outer type annotations, not the field's
    /// own definitions or annotations nested inside a function type.
    fn projection_domain(&mut self, mut domain: Expr) -> Result<Expr, NatDefinitionElabError> {
        use fln_core::name::LeafView;

        loop {
            self.tick()?;
            let ExprNode::App { f, a } = domain.node() else {
                return Ok(domain);
            };
            domain = match f.node() {
                ExprNode::Const { name, .. }
                    if name.parent().is_anonymous()
                        && matches!(
                            name.leaf_view(),
                            LeafView::Str("outParam" | "semiOutParam")
                        ) =>
                {
                    a.clone()
                }
                ExprNode::App { f, a } => match f.node() {
                    ExprNode::Const { name, .. }
                        if name.parent().is_anonymous()
                            && matches!(
                                name.leaf_view(),
                                LeafView::Str("optParam" | "autoParam")
                            ) =>
                    {
                        a.clone()
                    }
                    _ => return Ok(domain),
                },
                _ => return Ok(domain),
            };
        }
    }
}

impl Context {
    /// Comparing function types must constrain the universes of their domains
    /// and codomains, not just the universe of the complete Pi. A whole-Pi
    /// constraint can hide a needed assignment behind a maximum: e.g.
    /// `Nat -> Nat` against `?A -> ?B` does not by itself tell the bounded
    /// universe solver that `?B : Type ?v` requires `?v = 0`.
    ///
    /// These are only inference obligations. The ordinary unifier still checks
    /// the original equation and K1 still validates every assignment. Do not
    /// decompose arbitrary applications: reducible heads can discard arguments.
    pub(super) fn constrain_telescope_universes(
        &mut self,
        actual: &Expr,
        expected: &Expr,
    ) -> Result<(), NatDefinitionElabError> {
        if !actual.has_expr_mvar()
            && !actual.has_level_mvar()
            && !expected.has_expr_mvar()
            && !expected.has_level_mvar()
        {
            return Ok(());
        }
        let saved = self.txn.lctx.clone();
        let result = self.telescope_universe_constraints(actual, expected);
        self.txn.lctx = saved;
        result
    }

    fn telescope_universe_constraints(
        &mut self,
        actual: &Expr,
        expected: &Expr,
    ) -> Result<(), NatDefinitionElabError> {
        let mut pending = vec![(actual.clone(), expected.clone(), self.txn.lctx.clone())];
        while let Some((left, right, scope)) = pending.pop() {
            self.tick()?;
            self.txn.lctx = scope;
            let left = self.instantiate(&left)?;
            let right = self.instantiate(&right)?;
            if let (Some(a), Some(b)) = (self.known_type(&left)?, self.known_type(&right)?)
                && (a.has_level_mvar() || b.has_level_mvar())
            {
                self.equations.push(SourceEquation::inference(a, b));
            }
            if let (
                ExprNode::ForallE {
                    binder_name,
                    binder_type: a,
                    body: ab,
                    binder_info,
                },
                ExprNode::ForallE {
                    binder_type: b,
                    body: bb,
                    ..
                },
            ) = (left.node(), right.node())
            {
                let outer = self.txn.lctx.clone();
                let id = FVarId(self.fresh_name()?);
                let local = Expr::fvar(id.clone());
                let ab = self.substitute(ab, &local)?;
                let bb = self.substitute(bb, &local)?;
                self.txn
                    .lctx
                    .add_param(id, binder_name.clone(), a.clone(), *binder_info);
                pending.push((ab, bb, self.txn.lctx.clone()));
                pending.push((a.clone(), b.clone(), outer));
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod projection_tests {
    use super::*;
    use crate::lctx::LocalDecl;
    use crate::records::{RecordBudget, RecordSpec, record_declarations};
    use fln_env::constants::{ConstantVal, DefinitionVal};
    use fln_env::environment::{DeclarationBudget, DeclarationCommitted};
    use fln_env::pmap::CollisionBudget;
    use fln_kernel::capability::{Published, admit};
    use fln_kernel::council::{Council, CouncilOutcome, convene};

    fn n(text: &str) -> Name {
        Name::from_components(text.split('.'))
    }

    fn c(text: &str) -> Expr {
        Expr::const_(n(text), Vec::new())
    }

    fn budget() -> Budget {
        Budget::for_stack_bytes(2 * 1024 * 1024)
    }

    fn local(name: &str, type_: Expr, index: usize) -> LocalDecl {
        LocalDecl {
            id: FVarId(n(name)),
            user_name: n(name),
            type_,
            value: None,
            binder_info: BinderInfo::Default,
            index,
        }
    }

    fn environment() -> Environment {
        let mut env = crate::seed::bootstrap_nat_environment(budget()).unwrap();
        let parameter_sort = Level::param(n("u")).succ().unwrap();
        let parameter = local("A", Expr::sort(parameter_sort.clone()), 0);
        let carrier = local("carrier", Expr::sort(Level::one()), 2);
        let declarations = record_declarations(
            &RecordSpec {
                name: n("Packet"),
                level_params: vec![n("u")],
                parameters: vec![parameter.clone()],
                fields: vec![
                    local("element", Expr::fvar(parameter.id), 1),
                    carrier.clone(),
                    local("payload", Expr::fvar(carrier.id), 3),
                ],
                result_level: Level::max(parameter_sort, Level::one().succ().unwrap()).unwrap(),
                is_class: false,
            },
            RecordBudget::default(),
        )
        .unwrap();
        for declaration in declarations {
            let Outcome::Complete(admitted) = admit(&env, declaration, budget()) else {
                panic!("record fixture did not complete");
            };
            let CouncilOutcome::Agreed(checked) = convene(&Council::nobody_was_asked(), admitted)
            else {
                panic!("record fixture was not accepted");
            };
            env = match checked.publish(
                DeclarationBudget::default(),
                CollisionBudget::default(),
                None,
            ) {
                Outcome::Complete(Published::Committed(DeclarationCommitted::Published(
                    result,
                ))) => result.environment,
                Outcome::Complete(Published::BlockCommitted(result)) => result.environment,
                other => panic!("record fixture publication failed: {other:?}"),
            };
        }
        env
    }

    fn packet(level: Level, parameter: Expr) -> Expr {
        Expr::app(Expr::const_(n("Packet"), vec![level]), parameter)
    }

    fn field(index: u64, receiver: Expr) -> Expr {
        Expr::proj(n("Packet"), index, receiver)
    }

    #[test]
    fn primitive_projection_types_instantiate_parameters_and_earlier_fields() {
        let env = environment();
        let mut context = Context::new(&env, budget());
        let receiver = FVarId(n("p"));
        context.txn.lctx.add_param(
            receiver.clone(),
            n("p"),
            packet(Level::zero(), c("Nat")),
            BinderInfo::Default,
        );
        let value = Expr::fvar(receiver);
        assert_eq!(
            context.known_type(&field(0, value.clone())).unwrap(),
            Some(c("Nat"))
        );
        assert_eq!(
            context.known_type(&field(1, value.clone())).unwrap(),
            Some(Expr::sort(Level::one()))
        );
        assert_eq!(
            context.known_type(&field(2, value.clone())).unwrap(),
            Some(field(1, value))
        );

        let type_receiver = FVarId(n("types"));
        context.txn.lctx.add_param(
            type_receiver.clone(),
            n("types"),
            packet(Level::one(), Expr::sort(Level::one())),
            BinderInfo::Default,
        );
        assert_eq!(
            context
                .known_type(&field(0, Expr::fvar(type_receiver)))
                .unwrap(),
            Some(Expr::sort(Level::one()))
        );
    }

    #[test]
    fn dependent_projection_under_a_binder_reconstructs_a_kernel_checked_type() {
        let env = environment();
        let mut context = Context::new(&env, budget());
        let domain = packet(Level::zero(), c("Nat"));
        let value = Expr::lam(
            n("p"),
            domain.clone(),
            field(2, Expr::bvar(0).unwrap()),
            BinderInfo::Default,
        );
        let expected = Expr::forall_e(
            n("p"),
            domain,
            field(1, Expr::bvar(0).unwrap()),
            BinderInfo::Default,
        );
        assert_eq!(context.known_type(&value).unwrap(), Some(expected.clone()));
        assert!(context.txn.lctx.is_empty());
        let declaration = Declaration::Defn(DefinitionVal {
            base: ConstantVal {
                name: n("payload"),
                level_params: Vec::new(),
                type_: expected,
            },
            value,
            hints: ReducibilityHints::Abbrev,
            safety: DefinitionSafety::Safe,
            all: vec![n("payload")],
        });
        assert!(matches!(
            fln_kernel::check(&env, &declaration, budget()),
            Outcome::Complete(Verdict::Accepted { .. })
        ));
    }

    #[test]
    fn invalid_primitive_projections_do_not_acquire_an_inferred_type() {
        let env = environment();
        let mut context = Context::new(&env, budget());
        let receiver = FVarId(n("p"));
        context.txn.lctx.add_param(
            receiver.clone(),
            n("p"),
            packet(Level::zero(), c("Nat")),
            BinderInfo::Default,
        );
        let value = Expr::fvar(receiver);
        for expression in [
            Expr::proj(n("Other"), 0, value.clone()),
            field(3, value.clone()),
            field(u64::MAX, value),
            field(0, c("Nat.zero")),
        ] {
            assert_eq!(context.known_type(&expression).unwrap(), None);
        }
        assert!(context.txn.mvars.assignments().is_empty());
    }

    #[test]
    fn projection_budget_stops_restore_the_outer_local_context() {
        let env = environment();
        let domain = packet(Level::zero(), c("Nat"));
        let expression = Expr::lam(
            n("p"),
            domain,
            field(2, Expr::bvar(0).unwrap()),
            BinderInfo::Default,
        );
        let make_context = || {
            let mut context = Context::new(&env, budget());
            context.txn.lctx.add_param(
                FVarId(n("ambient")),
                n("ambient"),
                c("Nat"),
                BinderInfo::Default,
            );
            context
        };
        let mut completed = make_context();
        assert!(completed.known_type(&expression).unwrap().is_some());
        let used = completed.txn.budget.heartbeats_consumed;
        assert!(used > 1);
        for limit in 1..used {
            let mut context = make_context();
            let before = context.txn.lctx.clone();
            context.txn.budget.max_heartbeats = limit;
            assert!(context.known_type(&expression).is_err(), "budget {limit}");
            assert_eq!(context.txn.lctx, before, "budget {limit}");
            assert!(context.txn.mvars.assignments().is_empty(), "budget {limit}");
        }
    }
}

#[cfg(test)]
mod telescope_tests {
    use super::*;

    #[test]
    fn every_budget_stop_restores_the_ambient_local_context() {
        let parameter = Name::from_components(["ambient"]);
        let domain = Expr::sort(Level::mvar(LMVarId(Name::from_components(["unknown"]))));
        let fixed = Expr::sort(Level::one());
        let left = Expr::forall_e(
            parameter.clone(),
            domain.clone(),
            domain,
            BinderInfo::Default,
        );
        let right = Expr::forall_e(
            parameter.clone(),
            fixed.clone(),
            fixed.clone(),
            BinderInfo::Default,
        );
        let make_context = || {
            let mut context = Context::new(
                &Environment::new(),
                Budget::for_stack_bytes(2 * 1024 * 1024),
            );
            context.txn.lctx.add_param(
                FVarId(parameter.clone()),
                parameter.clone(),
                fixed.clone(),
                BinderInfo::Default,
            );
            context
        };
        let mut control = make_context();
        let initial = control.txn.lctx.clone();
        control
            .constrain_telescope_universes(&left, &right)
            .unwrap();
        assert_eq!(control.txn.lctx, initial);
        let work = control.txn.budget.heartbeats_consumed;
        assert!(work > 0);
        // A zero heartbeat limit intentionally means unlimited.
        for limit in 1..work {
            let mut stopped = make_context();
            stopped.txn.budget.max_heartbeats = limit;
            assert!(
                stopped
                    .constrain_telescope_universes(&left, &right)
                    .is_err(),
                "{limit}"
            );
            assert_eq!(stopped.txn.lctx, initial, "{limit}");
            assert!(stopped.txn.mvars.assignments().is_empty());
        }
    }
}
