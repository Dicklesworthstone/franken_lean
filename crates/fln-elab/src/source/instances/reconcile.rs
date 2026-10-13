//! A selected instance may determine an earlier, opaque dictionary output.
//!
//! This is the narrow post-selection counterpart of the Reference's
//! `assignOutParams` / `withAssignableSyntheticOpaque`. Ordinary unification,
//! candidate selection, unrelated instance holes and tactic goals stay opaque.
//! The unchanged transactional solver checks every proposed assignment in K1.
use super::*;
use std::collections::HashSet;

impl Context {
    fn instance_output_holes(
        &mut self,
        frame: &Frame,
        expected: &Expr,
    ) -> Result<Vec<MVarId>, NatDefinitionElabError> {
        let mut pending = HashSet::new();
        for index in 0..self.instance_goals.len() {
            self.tick()?;
            pending.insert(self.instance_goals[index].clone());
        }
        let mut key = &frame.key;
        let mut target = expected;
        let mut roots = Vec::new();
        // Only actual output slots receive permission. Semi-outputs use other
        // placeholders and ordinary inputs have already passed readiness checks.
        while let (ExprNode::App { f: kf, a: ka }, ExprNode::App { f: tf, a: ta }) =
            (key.node(), target.node())
        {
            self.tick()?;
            if matches!(ka.node(), ExprNode::BVar { idx: 0 }) {
                roots.push(ta.clone());
            }
            key = kf;
            target = tf;
        }
        let mut seen = HashSet::new();
        let mut identified = HashSet::new();
        let mut holes = Vec::new();
        while let Some(expr) = roots.pop() {
            self.tick()?;
            if !expr.has_expr_mvar() || !seen.insert(expr.allocation_identity()) {
                continue;
            }
            match expr.node() {
                ExprNode::MVar { id } if pending.contains(id) => {
                    let decl = self
                        .txn
                        .mvars
                        .get_decl(id)
                        .ok_or_else(|| failure(SourceInferenceError::Scope))?;
                    if decl.kind == MetavarKind::SyntheticOpaque
                        && !self.txn.mvars.is_assigned(id)
                        && identified.insert(id.clone())
                    {
                        holes.push(id.clone());
                    }
                }
                ExprNode::App { f, a } => {
                    roots.push(a.clone());
                    roots.push(f.clone());
                }
                ExprNode::Lam {
                    binder_type, body, ..
                }
                | ExprNode::ForallE {
                    binder_type, body, ..
                } => {
                    roots.push(body.clone());
                    roots.push(binder_type.clone());
                }
                ExprNode::LetE {
                    type_, value, body, ..
                } => {
                    roots.push(body.clone());
                    roots.push(value.clone());
                    roots.push(type_.clone());
                }
                ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => {
                    roots.push(expr.clone());
                }
                _ => {}
            }
        }
        Ok(holes)
    }

    pub(super) fn reconcile_instance_outputs(
        &mut self,
        frame: &Frame,
        actual: Expr,
        expected: Expr,
    ) -> Result<(), NatDefinitionElabError> {
        let holes = self.instance_output_holes(frame, &expected)?;
        if holes.is_empty() {
            self.equations
                .push(SourceEquation::instance_result(actual, expected));
            return self.flush(true);
        }
        // No widened policy may apply to a suspended equation. Resolve those
        // first, then check this single selected-result equation in isolation.
        let mut trial = self.clone();
        let result = (|| {
            trial.flush(true)?;
            for id in &holes {
                trial.tick()?;
                trial
                    .txn
                    .mvars
                    .set_kind(id, MetavarKind::Synthetic)
                    .map_err(|e| {
                        failure(SourceInferenceError::Unification(Box::new(
                            UnificationError::Metavariable(e),
                        )))
                    })?;
            }
            trial
                .unify_source_batch(&[(actual, expected)], true)
                .map_err(|e| failure(SourceInferenceError::Unification(Box::new(e))))?;
            // Kinds describe persistent elaboration policy, not a one-call
            // exception. Restore them even for outputs left unsolved by defeq.
            for id in &holes {
                trial.tick()?;
                trial
                    .txn
                    .mvars
                    .set_kind(id, MetavarKind::SyntheticOpaque)
                    .map_err(|e| {
                        failure(SourceInferenceError::Unification(Box::new(
                            UnificationError::Metavariable(e),
                        )))
                    })?;
            }
            Ok(())
        })();
        self.txn.budget.heartbeats_consumed = trial.txn.budget.heartbeats_consumed;
        result?;
        *self = trial;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::records::{RecordBudget, RecordSpec, record_declarations};
    use fln_env::environment::{DeclarationBudget, DeclarationCommitted, Environment};
    use fln_env::pmap::CollisionBudget;
    use fln_kernel::capability::{Published, admit};
    use fln_kernel::council::{Council, CouncilOutcome, convene};

    fn name(s: &str) -> Name {
        Name::from_components(s.split('.'))
    }
    fn constant(s: &str) -> Expr {
        Expr::const_(name(s), vec![])
    }
    fn apply(s: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
        args.into_iter().fold(constant(s), Expr::app)
    }
    fn inhabited(alpha: Expr) -> Expr {
        Expr::app(Expr::const_(name("Inhabited"), vec![Level::one()]), alpha)
    }
    fn dictionary(n: u64) -> Expr {
        [
            constant("Nat"),
            Expr::lit(Literal::Nat(fln_core::expr::NatLit::from_u64(n))),
        ]
        .into_iter()
        .fold(
            Expr::const_(name("Inhabited.mk"), vec![Level::one()]),
            Expr::app,
        )
    }
    fn publish(env: &Environment, declaration: Declaration) -> Environment {
        let Outcome::Complete(admitted) =
            admit(env, declaration, Budget::for_stack_bytes(2 * 1024 * 1024))
        else {
            panic!("fixture admission did not answer");
        };
        let CouncilOutcome::Agreed(checked) = convene(&Council::nobody_was_asked(), admitted)
        else {
            panic!("fixture was not accepted");
        };
        match checked.publish(
            DeclarationBudget::default(),
            CollisionBudget::default(),
            None,
        ) {
            Outcome::Complete(Published::BlockCommitted(p)) => p.environment,
            Outcome::Complete(Published::Committed(DeclarationCommitted::Published(p))) => {
                p.environment
            }
            other => panic!("fixture publication: {other:?}"),
        }
    }
    fn fixture() -> (Context, Frame, Expr, MVarId, MVarId) {
        let budget = Budget::for_stack_bytes(2 * 1024 * 1024);
        let mut env = crate::seed::bootstrap_nat_environment(budget).unwrap();
        for d in [
            crate::seed::out_param_seed_declaration(),
            crate::seed::inhabited::inhabited_seed_declaration(),
        ] {
            env = publish(&env, d);
        }
        let mut locals = LocalContext::new();
        let alpha = locals
            .add_param(
                FVarId(name("alpha")),
                name("alpha"),
                Expr::app(
                    Expr::const_(name("outParam"), vec![Level::one().succ().unwrap()]),
                    Expr::sort(Level::one()),
                ),
                BinderInfo::Default,
            )
            .clone();
        let d = locals
            .add_param(
                FVarId(name("dictionary")),
                name("dictionary"),
                inhabited(Expr::fvar(alpha.id.clone())),
                BinderInfo::InstImplicit,
            )
            .clone();
        for declaration in record_declarations(
            &RecordSpec {
                name: name("Output"),
                level_params: vec![],
                parameters: vec![alpha, d],
                fields: vec![],
                result_level: Level::one(),
                is_class: true,
            },
            RecordBudget::default(),
        )
        .unwrap()
        {
            env = publish(&env, declaration);
        }
        env = crate::instances::register_class(&env, &name("Output")).unwrap();
        env = crate::instances::register_class(&env, &name("Inhabited")).unwrap();
        let registry = InstanceRegistry::read(&env).unwrap();
        let mut ctx = Context::new(&env, budget);
        let alpha = ctx.hole(Expr::sort(Level::one())).unwrap();
        let d = ctx.instance_hole(inhabited(alpha.clone())).unwrap();
        let ExprNode::MVar { id: dictionary } = d.node() else {
            unreachable!()
        };
        let dictionary = dictionary.clone();
        let expected = apply("Output", [alpha.clone(), d]);
        let root = ctx.instance_hole(expected.clone()).unwrap();
        let ExprNode::MVar { id } = root.node() else {
            unreachable!()
        };
        let ambient = ctx.txn.lctx.clone();
        let frame = ctx
            .instance_frame(id.clone(), &registry, &ambient, None, true)
            .unwrap()
            .unwrap();
        let ExprNode::MVar { id: alpha } = alpha.node() else {
            unreachable!()
        };
        (ctx, frame, expected, alpha.clone(), dictionary)
    }
    fn unchanged(ctx: &Context, before: &Context) {
        assert_eq!(ctx.txn.mvars, before.txn.mvars);
        assert_eq!(ctx.txn.universes, before.txn.universes);
        assert_eq!(ctx.txn.constraints, before.txn.constraints);
        assert_eq!(ctx.txn.lctx, before.txn.lctx);
        assert_eq!(ctx.txn.env, before.txn.env);
    }

    #[test]
    fn dependent_output_assignment_is_checked_and_does_not_change_persistent_kinds() {
        let (mut ctx, frame, expected, alpha, d) = fixture();
        let unrelated = ctx.instance_hole(inhabited(constant("Nat"))).unwrap();
        let ExprNode::MVar { id: unrelated } = unrelated.node() else {
            unreachable!()
        };
        let actual = apply("Output", [constant("Nat"), dictionary(7)]);
        // The ordinary solver must still defer this exact equation.
        assert!(
            ctx.unify_source_batch(&[(actual.clone(), expected.clone())], true)
                .is_err()
        );
        ctx.reconcile_instance_outputs(&frame, actual, expected)
            .unwrap();
        assert_eq!(
            ctx.txn.mvars.get_assigned_expr(&alpha),
            Some(&constant("Nat"))
        );
        assert_eq!(ctx.txn.mvars.get_assigned_expr(&d), Some(&dictionary(7)));
        assert_eq!(
            ctx.txn.mvars.get_decl(&d).unwrap().kind,
            MetavarKind::SyntheticOpaque
        );
        assert!(!ctx.txn.mvars.is_assigned(unrelated));
        assert!(
            ctx.unify_source_batch(&[(Expr::mvar(unrelated.clone()), dictionary(7))], true)
                .is_err()
        );
    }

    #[test]
    fn ill_typed_output_rolls_back_the_earlier_carrier_assignment() {
        let (mut ctx, frame, expected, _, _) = fixture();
        let before = ctx.clone();
        // Forged result metadata cannot assign a Nat value to an Inhabited Nat hole.
        let actual = apply("Output", [constant("Nat"), Expr::sort(Level::zero())]);
        let error = ctx
            .reconcile_instance_outputs(&frame, actual, expected)
            .unwrap_err();
        assert!(matches!(
            error,
            NatDefinitionElabError::Inference(SourceInferenceError::Unification(_))
        ));
        unchanged(&ctx, &before);
        assert!(ctx.txn.budget.heartbeats_consumed > before.txn.budget.heartbeats_consumed);
    }

    #[test]
    fn input_and_semi_output_slots_do_not_authorize_opaque_dictionary_assignment() {
        for index in [1, 2] {
            let (mut ctx, mut frame, expected, _, _) = fixture();
            let ExprNode::App { f, .. } = frame.key.node() else {
                unreachable!()
            };
            frame.key = Expr::app(f.clone(), Expr::bvar(index).unwrap());
            let before = ctx.clone();
            let actual = apply("Output", [constant("Nat"), dictionary(7)]);
            assert!(
                ctx.reconcile_instance_outputs(&frame, actual, expected)
                    .is_err()
            );
            unchanged(&ctx, &before);
        }
    }

    #[test]
    fn a_tactic_goal_in_an_output_position_is_not_an_instance_output() {
        let (mut ctx, frame, expected, _, d) = fixture();
        ctx.instance_goals.retain(|id| id != &d);
        let before = ctx.clone();
        assert!(
            ctx.reconcile_instance_outputs(
                &frame,
                apply("Output", [constant("Nat"), dictionary(7)]),
                expected
            )
            .is_err()
        );
        unchanged(&ctx, &before);
    }

    #[test]
    fn exhaustion_during_policy_restoration_discards_the_entire_speculation() {
        let (initial, frame, expected, _, _) = fixture();
        let actual = apply("Output", [constant("Nat"), dictionary(7)]);
        let mut control = initial.clone();
        control
            .reconcile_instance_outputs(&frame, actual.clone(), expected.clone())
            .unwrap();
        let mut limited = initial.clone();
        limited.txn.budget.max_heartbeats = control.txn.budget.heartbeats_consumed - 1;
        assert!(
            limited
                .reconcile_instance_outputs(&frame, actual, expected)
                .is_err()
        );
        unchanged(&limited, &initial);
        assert!(limited.txn.budget.heartbeats_consumed > initial.txn.budget.heartbeats_consumed);
    }
}
