//! Metered source weak-head reduction, with heap continuations for eliminators.
//!
//! This is an elaboration aid, not a checker. Constructor reduction uses only
//! admitted recursor rules. Stuck majors are rebuilt once and unwound, never
//! resubmitted in an unproductive loop. Neither reduction nor transparency can
//! publish a declaration or eliminate an original source typing obligation.
mod quotient;

use super::*;
use fln_env::constants::{ConstantInfo, RecursorVal};

enum Continuation {
    Quotient {
        head: Expr,
        arguments: Vec<Expr>,
        major: usize,
    },
    Projection {
        structure: Name,
        index: u64,
        arguments: Vec<Expr>,
    },
    Recursor {
        head: Expr,
        recursor: RecursorVal,
        arguments: Vec<Expr>,
    },
}

fn recursor_prefix(recursor: &RecursorVal) -> Result<usize, NatDefinitionElabError> {
    (recursor.num_params as usize)
        .checked_add(recursor.num_motives as usize)
        .and_then(|n| n.checked_add(recursor.num_minors as usize))
        .ok_or_else(|| failure(SourceInferenceError::ResourceLimit))
}

fn recursor_major(recursor: &RecursorVal) -> Result<usize, NatDefinitionElabError> {
    recursor_prefix(recursor)?
        .checked_add(recursor.num_indices as usize)
        .ok_or_else(|| failure(SourceInferenceError::ResourceLimit))
}

impl Context {
    pub(super) fn reduce_source_head(
        &mut self,
        expr: &Expr,
        transparency: UnificationTransparency,
        zeta_delta: bool,
    ) -> Result<Expr, NatDefinitionElabError> {
        let mut head = self.instantiate(expr)?;
        let original = head.clone();
        let mut changed = false;
        let mut arguments = Vec::new();
        let mut continuations = Vec::new();
        'reduce: loop {
            loop {
                self.tick()?;
                match head.node() {
                    ExprNode::Proj {
                        struct_name,
                        idx,
                        expr,
                    } => {
                        continuations.push(Continuation::Projection {
                            structure: struct_name.clone(),
                            index: *idx,
                            arguments: std::mem::take(&mut arguments),
                        });
                        head = expr.clone();
                    }
                    ExprNode::MData { expr, .. } => {
                        changed = true;
                        head = expr.clone();
                    }
                    ExprNode::App { f, a } => {
                        arguments.push(a.clone());
                        head = f.clone();
                    }
                    ExprNode::LetE { body, value, .. } => {
                        changed = true;
                        head = self.substitute(body, value)?;
                    }
                    ExprNode::Lam { body, .. } if !arguments.is_empty() => {
                        changed = true;
                        let value = arguments.pop().expect("guarded application");
                        head = self.substitute(body, &value)?;
                    }
                    ExprNode::FVar { id } if zeta_delta => {
                        let value = self.txn.lctx.find(id).and_then(|local| local.value.clone());
                        match value {
                            Some(value) => {
                                changed = true;
                                head = value;
                            }
                            None => break,
                        }
                    }
                    ExprNode::Const { name, levels } => match self.txn.env.find(name).cloned() {
                        Some(ConstantInfo::Defn(definition)) => {
                            if definition.safety != DefinitionSafety::Safe
                                || !match transparency {
                                    UnificationTransparency::None => false,
                                    UnificationTransparency::Abbreviations => {
                                        definition.hints == ReducibilityHints::Abbrev
                                    }
                                    UnificationTransparency::Instances => {
                                        definition.hints == ReducibilityHints::Abbrev
                                            || crate::reducibility::table(&self.txn.env)
                                                .map_err(|error| {
                                                    failure(SourceInferenceError::Unification(
                                                        Box::new(UnificationError::Reducibility(
                                                            error,
                                                        )),
                                                    ))
                                                })?
                                                .status(name)
                                                .unfolds_at_instances()
                                    }
                                    UnificationTransparency::SafeDefinitions => true,
                                }
                            {
                                break;
                            }
                            if definition.base.level_params.len() != levels.len() {
                                return Err(failure(SourceInferenceError::Scope));
                            }
                            changed = true;
                            head = self.instantiate_params(
                                &definition.value,
                                &definition.base.level_params,
                                levels,
                            )?;
                        }
                        Some(ConstantInfo::Quot(_)) => {
                            let Some(major) = self.source_quotient_major(&head, arguments.len())?
                            else {
                                break;
                            };
                            let value = arguments[arguments.len() - major - 1].clone();
                            continuations.push(Continuation::Quotient {
                                head,
                                arguments: std::mem::take(&mut arguments),
                                major,
                            });
                            head = value;
                        }
                        Some(ConstantInfo::Rec(recursor)) => {
                            let major = recursor_major(&recursor)?;
                            if recursor.is_unsafe
                                || recursor.all.is_empty()
                                || recursor.num_motives as usize != recursor.all.len()
                                || levels.len() != recursor.base.level_params.len()
                                || major >= arguments.len()
                            {
                                break;
                            }
                            let major_value = arguments[arguments.len() - major - 1].clone();
                            continuations.push(Continuation::Recursor {
                                head,
                                recursor,
                                arguments: std::mem::take(&mut arguments),
                            });
                            head = major_value;
                        }
                        _ => break,
                    },
                    _ => break,
                }
            }
            while let Some(continuation) = continuations.pop() {
                self.tick()?;
                match continuation {
                    Continuation::Quotient {
                        head: eliminator,
                        arguments: mut outer,
                        major,
                    } => {
                        if let Some(reduced) =
                            self.source_quotient_step(&eliminator, &outer, &head, &arguments)?
                        {
                            changed = true;
                            outer.truncate(outer.len() - major - 1);
                            head = reduced;
                            arguments = outer;
                            continue 'reduce;
                        }
                        let position = outer.len() - major - 1;
                        outer[position] = self.rebuild_application(head, arguments)?;
                        head = eliminator;
                        arguments = outer;
                    }
                    Continuation::Projection {
                        structure,
                        index,
                        arguments: outer,
                    } => {
                        if let Some(field) = crate::records::constructor_field(
                            &self.txn.env,
                            &structure,
                            index,
                            &head,
                            &arguments,
                        ) {
                            changed = true;
                            head = field;
                            arguments = outer;
                            continue 'reduce;
                        }
                        head = self.rebuild_application(head, arguments)?;
                        head = Expr::proj(structure, index, head);
                        arguments = outer;
                    }
                    Continuation::Recursor {
                        head: rec_head,
                        recursor,
                        arguments: mut outer,
                    } => {
                        let reduced =
                            self.source_iota(&rec_head, &recursor, &outer, &head, &arguments)?;
                        let reduced = match reduced {
                            Some(reduced) => Some(reduced),
                            None => self.source_k_iota(&rec_head, &recursor, &outer)?,
                        };
                        if let Some(reduced) = reduced {
                            changed = true;
                            let prefix = recursor_major(&recursor)?;
                            outer.truncate(outer.len() - prefix - 1);
                            head = reduced;
                            arguments = outer;
                            continue 'reduce;
                        }
                        let major = recursor_major(&recursor)?;
                        let position = outer.len() - major - 1;
                        outer[position] = self.rebuild_application(head, arguments)?;
                        head = rec_head;
                        arguments = outer;
                    }
                }
            }
            // A no-op query must not split sharing by rebuilding an unchanged
            // application spine. This matters when simp visits a shared DAG.
            return if changed {
                self.rebuild_application(head, arguments)
            } else {
                Ok(original)
            };
        }
    }

    /// An admitted nullary K recursor can reduce an unknown proof only when
    /// its spine-derived major domain is exactly the constructor result. This
    /// sufficient gate does not equate unknown indices or assign metavariables.
    /// Telescope substitution is capture-avoiding, including under open binders.
    fn source_k_iota(
        &mut self,
        head: &Expr,
        recursor: &RecursorVal,
        arguments: &[Expr],
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        if !recursor.k
            || recursor.all.len() != 1
            || recursor.num_motives != 1
            || recursor.rules.len() != 1
            || recursor.num_minors != 1
        {
            return Ok(None);
        }
        let ExprNode::Const { levels, .. } = head.node() else {
            return Ok(None);
        };
        let Some(ConstantInfo::Induct(family)) = self.txn.env.find(&recursor.all[0]).cloned()
        else {
            return Ok(None);
        };
        let rule = &recursor.rules[0];
        let Some(ConstantInfo::Ctor(ctor)) = self.txn.env.find(&rule.ctor).cloned() else {
            return Ok(None);
        };
        if family.is_unsafe
            || family.num_nested != 0
            || family.ctors != [rule.ctor.clone()]
            || family.all != recursor.all
            || family.num_indices != recursor.num_indices
            || family.num_params != recursor.num_params
            || ctor.is_unsafe
            || ctor.induct != family.base.name
            || ctor.num_params != family.num_params
            || ctor.num_fields != 0
            || rule.nfields != 0
        {
            return Ok(None);
        }
        let family_levels = if recursor.base.level_params == family.base.level_params {
            levels.as_slice()
        } else if recursor.base.level_params.len() == family.base.level_params.len() + 1
            && recursor.base.level_params[1..] == family.base.level_params
        {
            &levels[1..]
        } else {
            return Ok(None);
        };
        if ctor.base.level_params != family.base.level_params {
            return Ok(None);
        }
        let major = recursor_major(recursor)?;
        let mut domain =
            self.instantiate_params(&recursor.base.type_, &recursor.base.level_params, levels)?;
        for argument in arguments.iter().rev().take(major) {
            self.tick()?;
            let ExprNode::ForallE { body, .. } = domain.node() else {
                return Ok(None);
            };
            domain = self.substitute(body, argument)?;
        }
        let ExprNode::ForallE { binder_type, .. } = domain.node() else {
            return Ok(None);
        };
        let mut result =
            self.instantiate_params(&ctor.base.type_, &ctor.base.level_params, family_levels)?;
        for parameter in arguments.iter().rev().take(recursor.num_params as usize) {
            self.tick()?;
            let ExprNode::ForallE { body, .. } = result.node() else {
                return Ok(None);
            };
            result = self.substitute(body, parameter)?;
        }
        self.tick()?;
        if result != *binder_type {
            return Ok(None);
        }
        let mut value = self.instantiate_params(&rule.rhs, &recursor.base.level_params, levels)?;
        for argument in arguments.iter().rev().take(recursor_prefix(recursor)?) {
            self.tick()?;
            value = Expr::app(value, argument.clone());
        }
        Ok(Some(value))
    }

    fn rebuild_application(
        &mut self,
        mut head: Expr,
        arguments: Vec<Expr>,
    ) -> Result<Expr, NatDefinitionElabError> {
        for argument in arguments.into_iter().rev() {
            self.tick()?;
            head = Expr::app(head, argument);
        }
        Ok(head)
    }

    /// Ordinary constructor reduction for unnested single or mutual families.
    /// Unknown majors use the separate, sufficient K gate or remain stuck.
    fn source_iota(
        &mut self,
        rec_head: &Expr,
        recursor: &RecursorVal,
        arguments: &[Expr],
        major_head: &Expr,
        major_arguments: &[Expr],
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        let ExprNode::Const { levels, .. } = rec_head.node() else {
            return Ok(None);
        };
        // The owner is selected by the major's constructor and the recursor's
        // ordered rules. `all[0]` is only the first member of a mutual block.
        let family_name = match major_head.node() {
            ExprNode::Const { name, .. } => match self.txn.env.find(name) {
                Some(ConstantInfo::Ctor(ctor)) => ctor.induct.clone(),
                _ => return Ok(None),
            },
            ExprNode::Lit {
                literal: Literal::Nat(_),
            } if recursor.all == [Name::from_components(["Nat"])] => recursor.all[0].clone(),
            _ => return Ok(None),
        };
        let Some(ConstantInfo::Induct(family)) = self.txn.env.find(&family_name).cloned() else {
            return Ok(None);
        };
        if family.is_unsafe
            || family.num_indices != recursor.num_indices
            || family.num_nested != 0
            || family.num_params != recursor.num_params
            || family.all != recursor.all
            || recursor.rules.len() != family.ctors.len()
        {
            return Ok(None);
        }
        for (rule, constructor) in recursor.rules.iter().zip(&family.ctors) {
            self.tick()?;
            if &rule.ctor != constructor {
                return Ok(None);
            }
        }
        let mut members = std::collections::HashSet::new();
        let mut minors = 0usize;
        for member in &recursor.all {
            self.tick()?;
            let Some(ConstantInfo::Induct(info)) = self.txn.env.find(member) else {
                return Ok(None);
            };
            if !members.insert(member)
                || &info.base.name != member
                || info.is_unsafe
                || info.num_nested != 0
                || info.all != recursor.all
                || info.num_params != recursor.num_params
                || info.base.level_params != family.base.level_params
            {
                return Ok(None);
            }
            minors = minors
                .checked_add(info.ctors.len())
                .ok_or_else(|| failure(SourceInferenceError::ResourceLimit))?;
        }
        if !members.contains(&family_name)
            || recursor.num_motives as usize != members.len()
            || recursor.num_minors as usize != minors
        {
            return Ok(None);
        }
        let (constructor_name, constructor_levels, fields) = match major_head.node() {
            ExprNode::Const { name, levels } => {
                let Some(ConstantInfo::Ctor(ctor)) = self.txn.env.find(name).cloned() else {
                    return Ok(None);
                };
                if ctor.is_unsafe
                    || ctor.induct != family_name
                    || ctor.num_params != family.num_params
                    || !family.ctors.contains(name)
                    || ctor.base.level_params != family.base.level_params
                    || ctor.base.level_params.len() != levels.len()
                    || Some(major_arguments.len())
                        != (ctor.num_params as usize).checked_add(ctor.num_fields as usize)
                {
                    return Ok(None);
                }
                let fields = major_arguments
                    .iter()
                    .rev()
                    .skip(ctor.num_params as usize)
                    .cloned()
                    .collect::<Vec<_>>();
                (name.clone(), levels.clone(), fields)
            }
            ExprNode::Lit {
                literal: Literal::Nat(value),
            } if major_arguments.is_empty()
                && family_name == Name::from_components(["Nat"])
                && family.num_params == 0
                && family.base.level_params.is_empty() =>
            {
                // Retain the predecessor as a compact literal. Charge all input
                // limbs before the arithmetic module allocates proportional data.
                let zero = Name::from_components(["Nat", "zero"]);
                let successor = Name::from_components(["Nat", "succ"]);
                if family.ctors != [zero.clone(), successor.clone()] || !family.is_rec {
                    return Ok(None);
                }
                if value.limbs_le().is_empty() {
                    (zero, Vec::new(), Vec::new())
                } else {
                    for _ in value.limbs_le() {
                        self.tick()?;
                    }
                    let previous = fln_bignum::nat::BigNatView::from_limbs_le(value.limbs_le())
                        .sub(fln_bignum::nat::BigNatView::from_limbs_le(&[1]));
                    let literal = fln_bignum::interop::literal_from_bignat(&previous);
                    (
                        successor,
                        Vec::new(),
                        vec![Expr::lit(Literal::Nat(literal))],
                    )
                }
            }
            _ => return Ok(None),
        };
        let Some(ConstantInfo::Ctor(ctor)) = self.txn.env.find(&constructor_name) else {
            return Ok(None);
        };
        if ctor.is_unsafe
            || ctor.induct != family_name
            || ctor.num_fields as usize != fields.len()
            || ctor.num_params != family.num_params
        {
            return Ok(None);
        }
        let compatible = if recursor.base.level_params == family.base.level_params {
            *levels == constructor_levels
        } else {
            recursor.base.level_params.len() == family.base.level_params.len() + 1
                && recursor.base.level_params[1..] == family.base.level_params
                && levels.len() == constructor_levels.len() + 1
                && levels[1..] == constructor_levels
        };
        if !compatible {
            return Ok(None);
        }
        let Some(rule) = recursor
            .rules
            .iter()
            .find(|rule| rule.ctor == constructor_name)
            .cloned()
        else {
            return Ok(None);
        };
        if rule.nfields as usize != fields.len() {
            return Ok(None);
        }
        let mut result = self.instantiate_params(&rule.rhs, &recursor.base.level_params, levels)?;
        let prefix = recursor_prefix(recursor)?;
        for argument in arguments.iter().rev().take(prefix).chain(fields.iter()) {
            self.tick()?;
            result = Expr::app(result, argument.clone());
        }
        Ok(Some(result))
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

    fn environment() -> Environment {
        let budget = Budget::for_stack_bytes(2 * 1024 * 1024);
        let mut env = Environment::new();
        for declaration in [
            crate::seed::nat_inductive_seed_declaration(),
            crate::seed::bool_seed_declaration(),
        ] {
            let Outcome::Complete(admitted) = admit(&env, declaration, budget) else {
                panic!("kernel nonanswer");
            };
            let CouncilOutcome::Agreed(checked) = convene(&Council::nobody_was_asked(), admitted)
            else {
                panic!("kernel rejection");
            };
            let Outcome::Complete(Published::BlockCommitted(publication)) = checked.publish(
                DeclarationBudget::default(),
                CollisionBudget::default(),
                None,
            ) else {
                panic!("publication refused");
            };
            env = publication.environment;
        }
        env
    }
    fn bool_() -> Expr {
        Expr::const_(Name::from_components(["Bool"]), Vec::new())
    }
    fn truth() -> Expr {
        Expr::const_(Name::from_components(["Bool", "true"]), Vec::new())
    }
    fn select(major: Expr) -> Expr {
        let motive = Expr::lam(Name::anonymous(), bool_(), bool_(), BinderInfo::Default);
        let mut expr = Expr::const_(Name::from_components(["Bool", "rec"]), vec![Level::one()]);
        for value in [
            motive,
            Expr::const_(Name::from_components(["Bool", "false"]), Vec::new()),
            truth(),
            major,
        ] {
            expr = Expr::app(expr, value);
        }
        expr
    }
    #[test]
    fn source_iota_budget_exhaustion_is_typed_and_does_not_publish_state() {
        let env = environment();
        let input = select(select(truth()));
        let mut control = Context::new(&env, Budget::DEFAULT);
        assert_eq!(control.whnf(&input).unwrap(), truth());
        let spent = control.txn.budget.heartbeats_consumed;
        let mut limited = Context::new(&env, Budget::DEFAULT);
        limited.txn.budget.max_heartbeats = spent - 1;
        assert!(matches!(
            limited.whnf(&input),
            Err(NatDefinitionElabError::Inference(
                SourceInferenceError::ResourceLimit
            ))
        ));
        assert_eq!(limited.txn.env, env);
        assert!(limited.txn.mvars.is_empty());
        assert_eq!(
            Context::new(&env, Budget::DEFAULT).whnf(&input).unwrap(),
            truth()
        );
    }
    #[test]
    fn variable_and_foreign_constructor_majors_stay_stuck() {
        let env = environment();
        let mut ctx = Context::new(&env, Budget::DEFAULT);
        let local = FVarId(Name::from_components(["flag"]));
        ctx.txn
            .lctx
            .add_param(local.clone(), local.0.clone(), bool_(), BinderInfo::Default);
        for major in [
            Expr::fvar(local),
            Expr::const_(Name::from_components(["Nat", "zero"]), Vec::new()),
            Expr::lit(Literal::Nat(NatLit::from_u64(0))),
        ] {
            let input = select(major);
            assert_eq!(ctx.whnf(&input).unwrap(), input);
        }
    }
    #[test]
    fn recursor_normalization_respects_local_let_unfolding_policy() {
        let env = environment();
        let mut ctx = Context::new(&env, Budget::DEFAULT);
        let local = FVarId(Name::from_components(["flag"]));
        ctx.txn
            .lctx
            .add_let(local.clone(), local.0.clone(), bool_(), truth());
        let input = select(Expr::fvar(local));
        assert_eq!(
            ctx.whnf_with_transparency(&input, UnificationTransparency::None, false)
                .unwrap(),
            input
        );
        assert_eq!(
            ctx.whnf_with_transparency(&input, UnificationTransparency::None, true)
                .unwrap(),
            truth()
        );
    }
    #[test]
    fn deeply_nested_recursors_use_heap_continuations() {
        let env = environment();
        std::thread::Builder::new()
            .stack_size(64 * 1024)
            .spawn(move || {
                let mut input = truth();
                for _ in 0..10_000 {
                    input = select(input);
                }
                let mut ctx = Context::new(&env, Budget::for_stack_bytes(64 * 1024));
                assert_eq!(ctx.whnf(&input).unwrap(), truth());
            })
            .unwrap()
            .join()
            .unwrap();
    }

    fn conversion_environment() -> Environment {
        let budget = Budget::for_stack_bytes(2 * 1024 * 1024);
        let mut env = environment();
        for source in [
            "def Identity (A : Type) : Type := A",
            "def Forget (A : Type) : Type := Nat",
            "def Grow (A : Type) : Type := Nat -> A",
        ] {
            let checked = crate::check_definition_source(source.as_bytes(), &env, budget).unwrap();
            let Outcome::Complete(admitted) = admit(&env, checked.declaration, budget) else {
                panic!("alias admission nonanswer");
            };
            let CouncilOutcome::Agreed(checked) = convene(&Council::nobody_was_asked(), admitted)
            else {
                panic!("alias admission refused");
            };
            let Outcome::Complete(Published::Committed(
                fln_env::environment::DeclarationCommitted::Published(publication),
            )) = checked.publish(
                DeclarationBudget::default(),
                CollisionBudget::default(),
                None,
            )
            else {
                panic!("alias publication refused");
            };
            env = publication.environment;
        }
        env
    }

    fn alias(name: &str, argument: Expr) -> Expr {
        Expr::app(
            Expr::const_(Name::from_components([name]), vec![]),
            argument,
        )
    }

    #[test]
    fn source_typing_can_reduce_apparent_occurs_cycles_without_assigning_reflexive_holes() {
        let env = conversion_environment();
        for reversed in [false, true] {
            let mut ctx = Context::new(&env, Budget::DEFAULT);
            let hole = ctx.hole(Expr::sort(Level::one())).unwrap();
            let rhs = alias("Identity", hole.clone());
            let pair = if reversed {
                (rhs, hole.clone())
            } else {
                (hole.clone(), rhs)
            };
            ctx.unify_source_batch(&[pair], true).unwrap();
            assert!(ctx.txn.mvars.assignments().is_empty());
            assert_eq!(ctx.instantiate(&hole).unwrap(), hole);

            // Erasing the recursive occurrence must instead infer Nat, and the
            // ordinary assignment barrier must validate that concrete type.
            let rhs = alias("Forget", alias("Identity", hole.clone()));
            ctx.unify_source_batch(&[(hole.clone(), rhs)], true)
                .unwrap();
            assert_eq!(ctx.instantiate(&hole).unwrap(), nat_const());
            assert_eq!(ctx.txn.env, env);
        }
    }

    #[test]
    fn a_true_occurs_cycle_still_refuses_the_whole_source_typing_batch() {
        let env = conversion_environment();
        let mut ctx = Context::new(&env, Budget::DEFAULT);
        let first = ctx.hole(Expr::sort(Level::one())).unwrap();
        let cyclic = ctx.hole(Expr::sort(Level::one())).unwrap();
        let before = ctx.txn.clone();
        let error = ctx
            .unify_source_batch(
                &[
                    (first, nat_const()),
                    (cyclic.clone(), alias("Grow", alias("Identity", cyclic))),
                ],
                true,
            )
            .unwrap_err();
        assert!(matches!(
            error,
            UnificationError::Metavariable(MetavarError::OccursCheckFailed { .. })
        ));
        assert_eq!(ctx.txn.mvars, before.mvars);
        assert_eq!(ctx.txn.universes, before.universes);
        assert_eq!(ctx.txn.env, before.env);
        assert!(ctx.txn.budget.heartbeats_consumed > before.budget.heartbeats_consumed);
    }

    #[test]
    fn source_occurs_retry_never_widens_selection_or_turns_exhaustion_into_success() {
        let env = conversion_environment();
        let mut selection = Context::new(&env, Budget::DEFAULT);
        let hole = selection.hole(Expr::sort(Level::one())).unwrap();
        selection.equations.push(SourceEquation::selection(
            hole.clone(),
            alias("Identity", hole),
        ));
        let before = selection.txn.clone();
        assert!(matches!(
            selection.flush(true),
            Err(NatDefinitionElabError::Inference(
                SourceInferenceError::Unification(_)
            ))
        ));
        assert_eq!(selection.txn.mvars, before.mvars);
        assert_eq!(selection.equations.len(), 1);

        let mut limited = Context::new(&env, Budget::DEFAULT);
        let hole = limited.hole(Expr::sort(Level::one())).unwrap();
        let before = limited.txn.mvars.clone();
        limited.txn.budget.max_heartbeats = limited.txn.budget.heartbeats_consumed;
        assert!(matches!(
            limited.unify_source_batch(&[(hole.clone(), alias("Forget", hole))], true),
            Err(UnificationError::HeartbeatLimit)
        ));
        assert_eq!(limited.txn.mvars, before);
        assert_eq!(limited.txn.env, env);
    }
}

#[cfg(test)]
mod source_k_tests {
    use super::*;
    use fln_core::expr::NatLit;
    use fln_core::outcome::Outcome;
    use fln_env::environment::DeclarationBudget;
    use fln_env::pmap::CollisionBudget;
    use fln_kernel::capability::{Published, admit};
    use fln_kernel::council::{Council, CouncilOutcome, convene};

    fn environment() -> Environment {
        let budget = Budget::for_stack_bytes(1024 * 1024);
        let env = crate::seed::bootstrap_nat_environment(budget).unwrap();
        let declaration = crate::seed::equality::eq_seed_declaration();
        let Outcome::Complete(admitted) = admit(&env, declaration, budget) else {
            panic!("Eq admission");
        };
        let CouncilOutcome::Agreed(checked) = convene(&Council::nobody_was_asked(), admitted)
        else {
            panic!("Eq checking");
        };
        let Outcome::Complete(Published::BlockCommitted(publication)) = checked.publish(
            DeclarationBudget::default(),
            CollisionBudget::default(),
            None,
        ) else {
            panic!("Eq publication");
        };
        publication.environment
    }
    fn nat() -> Expr {
        Expr::const_(Name::from_components(["Nat"]), vec![])
    }
    fn number(value: u64) -> Expr {
        Expr::lit(Literal::Nat(NatLit::from_u64(value)))
    }
    fn cast(left: Expr, right: Expr, value: Expr) -> Expr {
        let equality = [nat(), left.clone(), Expr::bvar(0).unwrap()]
            .into_iter()
            .fold(
                Expr::const_(Name::from_components(["Eq"]), vec![Level::one()]),
                Expr::app,
            );
        let motive = Expr::lam(
            Name::anonymous(),
            nat(),
            Expr::lam(Name::anonymous(), equality, nat(), BinderInfo::Default),
            BinderInfo::Default,
        );
        [
            nat(),
            left,
            motive,
            value,
            right,
            Expr::fvar(FVarId(Name::from_components(["unknown_evidence"]))),
        ]
        .into_iter()
        .fold(
            Expr::const_(
                Name::from_components(["Eq", "rec"]),
                vec![Level::one(), Level::one()],
            ),
            Expr::app,
        )
    }
    #[test]
    fn source_k_reduction_requires_the_actual_endpoint_equation() {
        let env = environment();
        let mut context = Context::new(&env, Budget::DEFAULT);
        assert_eq!(
            context
                .whnf(&cast(number(7), number(7), number(9)))
                .unwrap(),
            number(9)
        );
        let different = cast(number(7), number(8), number(9));
        assert_eq!(context.whnf(&different).unwrap(), different);
    }
    #[test]
    fn source_k_telescope_substitution_preserves_all_external_binders() {
        let env = environment();
        for left in 0..5 {
            for right in 0..5 {
                let mut context = Context::new(&env, Budget::DEFAULT);
                let input = cast(
                    Expr::bvar(left).unwrap(),
                    Expr::bvar(right).unwrap(),
                    number(9),
                );
                let result = context.whnf(&input).unwrap();
                assert_eq!(result == number(9), left == right);
            }
        }
    }
    #[test]
    fn source_k_budget_failure_restores_no_semantic_state_and_can_recover() {
        let env = environment();
        let mut context = Context::new(&env, Budget::DEFAULT);
        let input = cast(number(7), number(7), number(9));
        context.txn.budget.max_heartbeats = 1;
        let before = context.txn.env.clone();
        assert!(matches!(
            context.whnf(&input),
            Err(NatDefinitionElabError::Inference(
                SourceInferenceError::ResourceLimit
            ))
        ));
        assert_eq!(context.txn.env, before);
        context.txn.budget.max_heartbeats = 200_000;
        assert_eq!(context.whnf(&input).unwrap(), number(9));
    }
    #[test]
    fn source_k_chains_use_the_heap_reduction_worklist() {
        // Only the reduction is the subject of the 64 KiB stack. The environment (the
        // seed's kernel admission) is built on this test's own thread: built inside, the
        // test overflowed whenever it ran before anything else in the binary, aborting
        // every other lib test of that run.
        let env = environment();
        std::thread::Builder::new()
            .stack_size(64 * 1024)
            .spawn(move || {
                let mut context = Context::new(&env, Budget::for_stack_bytes(64 * 1024));
                context.txn.budget.max_heartbeats = 5_000_000;
                let mut input = number(9);
                for _ in 0..512 {
                    input = cast(number(7), number(7), input);
                }
                assert_eq!(context.whnf(&input).unwrap(), number(9));
            })
            .unwrap()
            .join()
            .unwrap();
    }
}
