//! Constructor equality through ordinary recursors and equality transport.
//!
//! A recursor computes a continuation type: equal constructors supply field
//! equalities to a continuation, and distinct constructors supply the target
//! itself. Equality transport moves the reflexive continuation to the right
//! constructor. Dependent fields use HEq rather than an ill-typed homogeneous
//! equality. All terms remain candidates checked by both admission engines.
use super::equality::{equation, reflexivity};
use super::*;
use fln_env::constants::{ConstantInfo, ConstructorVal, InductiveVal, RecursorVal};

fn apps(head: Expr, arguments: impl IntoIterator<Item = Expr>) -> Expr {
    arguments.into_iter().fold(head, Expr::app)
}
fn fv(local: &LocalDecl) -> Expr {
    Expr::fvar(local.id.clone())
}

struct ConstructorView {
    constructor: ConstructorVal,
    levels: Vec<Level>,
    parameters: Vec<Expr>,
    fields: Vec<Typed>,
}
struct FamilyView {
    family: InductiveVal,
    recursor: RecursorVal,
    indices: Vec<Expr>,
}
#[derive(Clone)]
struct FieldRelation {
    universe: Level,
    heterogeneous: bool,
}
impl FieldRelation {
    fn type_(&self, left: &Typed, right: &Typed) -> Expr {
        if self.heterogeneous {
            apps(
                Expr::const_(Name::from_components(["HEq"]), vec![self.universe.clone()]),
                [
                    left.type_.clone(),
                    left.value.clone(),
                    right.type_.clone(),
                    right.value.clone(),
                ],
            )
        } else {
            equation(
                self.universe.clone(),
                left.type_.clone(),
                left.value.clone(),
                right.value.clone(),
            )
        }
    }
    fn refl(&self, value: &Typed) -> Expr {
        if self.heterogeneous {
            apps(
                Expr::const_(
                    Name::from_components(["HEq", "refl"]),
                    vec![self.universe.clone()],
                ),
                [value.type_.clone(), value.value.clone()],
            )
        } else {
            reflexivity(
                self.universe.clone(),
                value.type_.clone(),
                value.value.clone(),
            )
        }
    }
}
struct ConstructorEvidence {
    proof: Expr,
    relations: Vec<Expr>,
    clash: bool,
}

impl Context {
    fn constructor_spine(
        &mut self,
        expr: &Expr,
    ) -> Result<(Expr, Vec<Expr>), NatDefinitionElabError> {
        let mut head = self.whnf(expr)?;
        let mut arguments = Vec::new();
        loop {
            self.tick()?;
            match head.node() {
                ExprNode::MData { expr, .. } => head = expr.clone(),
                ExprNode::App { f, a } => {
                    arguments.push(a.clone());
                    head = f.clone();
                }
                _ => break,
            }
        }
        arguments.reverse();
        Ok((head, arguments))
    }

    fn constructor_view(&mut self, expr: &Expr) -> Result<ConstructorView, NatDefinitionElabError> {
        let (mut head, mut arguments) = self.constructor_spine(expr)?;
        if let ExprNode::Lit {
            literal: Literal::Nat(value),
        } = head.node()
        {
            if !arguments.is_empty() {
                return Err(error(TacticError::ConstructorEquality));
            }
            let zero = Name::from_components(["Nat", "zero"]);
            let succ = Name::from_components(["Nat", "succ"]);
            let Some(ConstantInfo::Induct(nat)) =
                self.txn.env.find(&Name::from_components(["Nat"]))
            else {
                return Err(error(TacticError::ConstructorEquality));
            };
            if nat.num_params != 0
                || nat.num_indices != 0
                || nat.ctors != [zero.clone(), succ.clone()]
                || !nat.is_rec
            {
                return Err(error(TacticError::ConstructorEquality));
            }
            if value.limbs_le().is_empty() {
                head = Expr::const_(zero, Vec::new());
            } else {
                for _ in value.limbs_le() {
                    self.tick()?;
                }
                let previous = fln_bignum::nat::BigNatView::from_limbs_le(value.limbs_le())
                    .sub(fln_bignum::nat::BigNatView::from_limbs_le(&[1]));
                arguments.push(Expr::lit(Literal::Nat(
                    fln_bignum::interop::literal_from_bignat(&previous),
                )));
                head = Expr::const_(succ, Vec::new());
            }
        }
        let ExprNode::Const { name, levels } = head.node() else {
            return Err(error(TacticError::ConstructorEquality));
        };
        let Some(ConstantInfo::Ctor(constructor)) = self.txn.env.find(name).cloned() else {
            return Err(error(TacticError::ConstructorEquality));
        };
        if constructor.is_unsafe
            || levels.len() != constructor.base.level_params.len()
            || arguments.len() != constructor.num_params as usize + constructor.num_fields as usize
            || arguments.len() > 1024
        {
            return Err(error(TacticError::ConstructorEquality));
        }
        let mut type_ = self.instantiate_params(
            &constructor.base.type_,
            &constructor.base.level_params,
            levels,
        )?;
        let mut fields = Vec::new();
        for (index, argument) in arguments.iter().enumerate() {
            self.tick()?;
            type_ = self.whnf(&type_)?;
            let ExprNode::ForallE {
                binder_type, body, ..
            } = type_.node()
            else {
                return Err(error(TacticError::ConstructorEquality));
            };
            if index >= constructor.num_params as usize {
                fields.push(Typed {
                    value: argument.clone(),
                    type_: binder_type.clone(),
                });
            }
            type_ = self.substitute(body, argument)?;
        }
        Ok(ConstructorView {
            parameters: arguments[..constructor.num_params as usize].to_vec(),
            fields,
            levels: levels.clone(),
            constructor,
        })
    }

    fn equality_family(
        &mut self,
        alpha: &Expr,
        left: &ConstructorView,
        right: &ConstructorView,
    ) -> Result<FamilyView, NatDefinitionElabError> {
        let (head, mut values) = self.constructor_spine(alpha)?;
        let ExprNode::Const { name, levels } = head.node() else {
            return Err(error(TacticError::ConstructorEquality));
        };
        let Some(ConstantInfo::Induct(family)) = self.txn.env.find(name).cloned() else {
            return Err(error(TacticError::ConstructorEquality));
        };
        let Some(ConstantInfo::Rec(recursor)) =
            self.txn.env.find(&Name::str(name.clone(), "rec")).cloned()
        else {
            return Err(error(TacticError::ConstructorEquality));
        };
        if family.is_unsafe
            || family.all != [name.clone()]
            || family.num_nested != 0
            || family.ctors.len() > 256
            || recursor.is_unsafe
            || recursor.all != family.all
            || recursor.num_motives != 1
            || recursor.num_minors as usize != family.ctors.len()
            || recursor.rules.len() != family.ctors.len()
            || recursor.num_params != family.num_params
            || recursor.num_indices != family.num_indices
            || values.len() != family.num_params as usize + family.num_indices as usize
            || &left.constructor.induct != name
            || &right.constructor.induct != name
            || !family.ctors.contains(&left.constructor.base.name)
            || !family.ctors.contains(&right.constructor.base.name)
            || left.levels != *levels
            || right.levels != *levels
            || recursor.base.level_params.len() != levels.len() + 1
            || recursor.base.level_params[1..] != family.base.level_params
        {
            return Err(error(TacticError::ConstructorEquality));
        }
        // Proof constructors are not disjoint/injective as data constructors:
        // proof irrelevance must never expose an existential's hidden witness.
        let kind = self
            .known_type(alpha)?
            .ok_or_else(|| error(TacticError::ConstructorEquality))?;
        let sort = self.whnf(&kind)?;
        if !matches!(sort.node(), ExprNode::Sort { level } if level.is_never_zero()) {
            return Err(error(TacticError::ConstructorEquality));
        }
        for ((left, right), actual) in left.parameters.iter().zip(&right.parameters).zip(&values) {
            if !self.proof_types_match(left, actual)? || !self.proof_types_match(right, actual)? {
                return Err(error(TacticError::ConstructorEquality));
            }
        }
        let indices = values.split_off(family.num_params as usize);
        Ok(FamilyView {
            family,
            recursor,
            indices,
        })
    }

    fn open_constructor_binder(
        &mut self,
        type_: &mut Expr,
    ) -> Result<LocalDecl, NatDefinitionElabError> {
        *type_ = self.whnf(type_)?;
        let ExprNode::ForallE {
            binder_type,
            body,
            binder_info,
            ..
        } = type_.node()
        else {
            return Err(error(TacticError::ConstructorEquality));
        };
        let mut local = self.equality_local(binder_type.clone())?;
        local.binder_info = *binder_info;
        local.index = self.txn.lctx.len();
        *type_ = self.substitute(body, &fv(&local))?;
        eliminate::add_local(&mut self.txn.lctx, &local);
        Ok(local)
    }

    fn type_universe(&mut self, value: &Expr) -> Result<Level, NatDefinitionElabError> {
        let type_ = self
            .known_type(value)?
            .ok_or_else(|| error(TacticError::ConstructorEquality))?;
        self.sort_level(&Typed {
            value: value.clone(),
            type_,
        })
    }

    fn close_constructor_locals(
        &mut self,
        locals: &[LocalDecl],
        mut value: Expr,
        lambda: bool,
    ) -> Result<Expr, NatDefinitionElabError> {
        for local in locals.iter().rev() {
            value = self.close_equality_binder(local, value, lambda)?;
        }
        Ok(value)
    }

    /// Construct a proof of `((field equalities -> target) -> target)` for a
    /// same-constructor equation, or of `target` for distinct constructors.
    /// The equality proof itself occurs in the resulting ordinary Eq.rec term.
    fn constructor_evidence(
        &mut self,
        witness: &Typed,
        target: &Expr,
    ) -> Result<ConstructorEvidence, NatDefinitionElabError> {
        // Selector construction opens temporary binders. Resource or typing
        // failures must not leave them visible to a later candidate attempt.
        let saved = self.txn.lctx.clone();
        let result = self.constructor_evidence_inner(witness, target);
        self.txn.lctx = saved;
        result
    }

    fn constructor_evidence_inner(
        &mut self,
        witness: &Typed,
        target: &Expr,
    ) -> Result<ConstructorEvidence, NatDefinitionElabError> {
        let equality_type = self.whnf(&witness.type_)?;
        let (level, alpha, original_left, original_right) = equality_target(&equality_type)
            .ok_or_else(|| error(TacticError::ConstructorEquality))?;
        let left = self.constructor_view(&original_left)?;
        let right = self.constructor_view(&original_right)?;
        let family = self.equality_family(&alpha, &left, &right)?;
        let universe = self.type_universe(target)?;
        let code_universe = universe
            .clone()
            .succ()
            .map_err(|_| failure(SourceInferenceError::Scope))?;
        let saved = self.txn.lctx.clone();

        let mut family_type = self.instantiate_params(
            &family.family.base.type_,
            &family.family.base.level_params,
            &left.levels,
        )?;
        for parameter in &left.parameters {
            family_type = self.whnf(&family_type)?;
            let ExprNode::ForallE { body, .. } = family_type.node() else {
                return Err(error(TacticError::ConstructorEquality));
            };
            family_type = self.substitute(body, parameter)?;
        }
        let mut index_locals = Vec::new();
        for _ in 0..family.family.num_indices {
            index_locals.push(self.open_constructor_binder(&mut family_type)?);
        }
        let generic_family = apps(
            Expr::const_(family.family.base.name.clone(), left.levels.clone()),
            left.parameters
                .iter()
                .cloned()
                .chain(index_locals.iter().map(fv)),
        );
        let major = self.equality_local(generic_family)?;
        let motive = self.close_equality_binder(&major, Expr::sort(universe.clone()), true)?;
        let motive = self.close_constructor_locals(&index_locals, motive, true)?;
        self.txn.lctx = saved.clone();
        let mut levels = vec![code_universe];
        levels.extend(left.levels.iter().cloned());
        let mut code = Typed {
            value: Expr::const_(family.recursor.base.name.clone(), levels.clone()),
            type_: self.instantiate_params(
                &family.recursor.base.type_,
                &family.recursor.base.level_params,
                &levels,
            )?,
        };
        for parameter in &left.parameters {
            let type_ = self
                .known_type(parameter)?
                .ok_or_else(|| error(TacticError::ConstructorEquality))?;
            code = self.match_apply(
                code,
                Typed {
                    value: parameter.clone(),
                    type_,
                },
            )?;
        }
        let motive_type = self
            .known_type(&motive)?
            .ok_or_else(|| error(TacticError::ConstructorEquality))?;
        code = self.match_apply(
            code,
            Typed {
                value: motive,
                type_: motive_type,
            },
        )?;
        let mut relations = Vec::new();
        for constructor_name in &family.family.ctors {
            self.txn.lctx = saved.clone();
            let Some(ConstantInfo::Ctor(constructor)) =
                self.txn.env.find(constructor_name).cloned()
            else {
                return Err(error(TacticError::ConstructorEquality));
            };
            let function_type = self.whnf(&code.type_)?;
            let ExprNode::ForallE { binder_type, .. } = function_type.node() else {
                return Err(error(TacticError::ConstructorEquality));
            };
            let minor_type = binder_type.clone();
            let mut open_type = minor_type.clone();
            let mut binders = Vec::new();
            for _ in 0..constructor.num_fields {
                binders.push(self.open_constructor_binder(&mut open_type)?);
            }
            let field_count = binders.len();
            // The remaining domains are recursive hypotheses, never evidence
            // available to the source tactic. They exist only in this minor.
            while matches!(self.whnf(&open_type)?.node(), ExprNode::ForallE { .. }) {
                self.tick()?;
                binders.push(self.open_constructor_binder(&mut open_type)?);
            }
            let body = if constructor_name == &left.constructor.base.name {
                if field_count != left.fields.len() {
                    return Err(error(TacticError::ConstructorEquality));
                }
                let mut equalities = Vec::new();
                for (field, old) in binders[..field_count].iter().zip(&left.fields) {
                    let universe = self.type_universe(&old.type_)?;
                    let heterogeneous = !self.proof_types_match(&old.type_, &field.type_)?;
                    let relation = FieldRelation {
                        universe,
                        heterogeneous,
                    };
                    let type_ = relation.type_(
                        old,
                        &Typed {
                            value: fv(field),
                            type_: field.type_.clone(),
                        },
                    );
                    equalities.push(self.equality_local(type_)?);
                    relations.push(relation);
                }
                let continuation =
                    self.close_constructor_locals(&equalities, target.clone(), false)?;
                let binder = self.equality_local(continuation)?;
                self.close_equality_binder(&binder, target.clone(), false)?
            } else {
                target.clone()
            };
            let minor = self.close_constructor_locals(&binders, body, true)?;
            self.txn.lctx = saved.clone();
            code = self.match_apply(
                code,
                Typed {
                    value: minor,
                    type_: minor_type,
                },
            )?;
        }
        // At the reflexive constructor, the continuation is supplied exactly
        // the reflexivity evidence for each (possibly dependent) field.
        let mut refl_locals = Vec::new();
        for (relation, field) in relations.iter().zip(&left.fields) {
            refl_locals.push(self.equality_local(relation.type_(field, field))?);
        }
        let continuation_type =
            self.close_constructor_locals(&refl_locals, target.clone(), false)?;
        let continuation = self.equality_local(continuation_type)?;
        let value = apps(
            fv(&continuation),
            relations.iter().zip(&left.fields).map(|(r, f)| r.refl(f)),
        );
        let base = self.close_equality_binder(&continuation, value, true)?;
        let code_prefix = apps(code.value, family.indices);
        let endpoint = self.equality_local(alpha.clone())?;
        let equation_local = self.equality_local(equation(
            level.clone(),
            alpha.clone(),
            original_left.clone(),
            fv(&endpoint),
        ))?;
        let motive = self.close_equality_binder(
            &equation_local,
            Expr::app(code_prefix, fv(&endpoint)),
            true,
        )?;
        let motive = self.close_equality_binder(&endpoint, motive, true)?;
        let proof = apps(
            Expr::const_(Name::from_components(["Eq", "rec"]), vec![universe, level]),
            [
                alpha,
                original_left,
                motive,
                base,
                original_right,
                witness.value.clone(),
            ],
        );
        let clash = left.constructor.base.name != right.constructor.base.name;
        let relations = if clash {
            Vec::new()
        } else {
            relations
                .iter()
                .zip(left.fields.iter().zip(&right.fields))
                .map(|(r, (a, b))| r.type_(a, b))
                .collect()
        };
        self.txn.lctx = saved;
        Ok(ConstructorEvidence {
            proof,
            relations,
            clash,
        })
    }

    pub(super) fn inject_dependent_proof_goal(
        &mut self,
        proof: &mut ProofState<'_>,
        goal: ProofGoal,
        witness: &Typed,
        labels: &[Name],
    ) -> Result<(), NatDefinitionElabError> {
        let evidence = self.constructor_evidence(witness, &goal.target)?;
        if evidence.clash {
            return self.close_proof_goal(goal, evidence.proof);
        }
        if labels.len() > evidence.relations.len() {
            return Err(error(TacticError::EliminationArity));
        }
        if evidence.relations.is_empty() {
            return Err(error(TacticError::ConstructorEquality));
        }
        let mut locals = Vec::new();
        for (index, type_) in evidence.relations.into_iter().enumerate() {
            let mut local = self.equality_local(type_)?;
            local.user_name = labels
                .get(index)
                .cloned()
                .unwrap_or_else(|| local.user_name.clone());
            locals.push(local);
        }
        let continuation_type =
            self.close_constructor_locals(&locals, goal.target.clone(), false)?;
        let (hole, mut child) = self.proof_goal(continuation_type)?;
        for mut local in locals {
            local.index = self.txn.lctx.len();
            eliminate::add_local(&mut self.txn.lctx, &local);
            child.introduced.push(local);
        }
        child.target = goal.target.clone();
        child.lctx = self.txn.lctx.clone();
        proof
            .work
            .push(Work::Close(goal, Expr::app(evidence.proof, hole)));
        proof.work.push(Work::Goal(child));
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use fln_env::environment::DeclarationBudget;
    use fln_env::pmap::CollisionBudget;
    use fln_kernel::capability::{Published, admit};
    use fln_kernel::council::{Council, CouncilOutcome, convene};

    fn environment() -> Environment {
        let mut env = Environment::new();
        for declaration in [
            crate::seed::nat_inductive_seed_declaration(),
            crate::seed::bool_seed_declaration(),
            crate::seed::eq_seed_declaration(),
            crate::seed::heq_seed_declaration(),
        ] {
            let Outcome::Complete(admitted) = admit(&env, declaration, Budget::DEFAULT) else {
                panic!("kernel did not complete");
            };
            let CouncilOutcome::Agreed(checked) = convene(&Council::nobody_was_asked(), admitted)
            else {
                panic!("kernel did not accept the seed");
            };
            let Outcome::Complete(Published::BlockCommitted(published)) = checked.publish(
                DeclarationBudget::default(),
                CollisionBudget::default(),
                None,
            ) else {
                panic!("checked block did not publish");
            };
            env = published.environment;
        }
        env
    }
    fn constant(parts: &[&str]) -> Expr {
        Expr::const_(Name::from_components(parts.iter().copied()), Vec::new())
    }
    fn witness(ctx: &mut Context, equal: bool) -> Typed {
        let mut h = ctx
            .equality_local(equation(
                Level::one(),
                constant(&["Bool"]),
                constant(&["Bool", "true"]),
                constant(&["Bool", if equal { "true" } else { "false" }]),
            ))
            .unwrap();
        h.index = ctx.txn.lctx.len();
        eliminate::add_local(&mut ctx.txn.lctx, &h);
        Typed {
            value: fv(&h),
            type_: h.type_,
        }
    }

    #[test]
    fn dependent_transport_construction_retains_scope_and_typed_work_stops() {
        let env = environment();
        let mut initial = Context::new(&env, Budget::DEFAULT);
        let h = witness(&mut initial, false);
        let original_locals = initial.txn.lctx.clone();
        let mut control = initial.clone();
        let evidence = control
            .constructor_evidence(&h, &constant(&["Nat"]))
            .unwrap();
        assert!(evidence.clash);
        assert!(evidence.relations.is_empty());
        assert_eq!(control.txn.lctx, original_locals);
        assert_eq!(control.txn.env, env);
        assert!(control.txn.mvars.is_empty());
        initial.txn.budget.max_heartbeats = control.txn.budget.heartbeats_consumed - 1;
        match initial.constructor_evidence(&h, &constant(&["Nat"])) {
            Err(NatDefinitionElabError::Inference(SourceInferenceError::ResourceLimit)) => {}
            Err(NatDefinitionElabError::Inference(SourceInferenceError::Unification(e)))
                if matches!(*e, UnificationError::HeartbeatLimit) => {}
            Err(other) => panic!("expected a work stop, got {other:?}"),
            Ok(_) => panic!("exhaustion must not become a proof candidate"),
        }
        assert_eq!(initial.txn.env, env);
        assert_eq!(initial.txn.lctx, original_locals);
    }
}
