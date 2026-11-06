//! Constructor-alternative splitters for annotated source matches.
//!
//! `generalizeTargetsEq` and `Cases.unifyEqs?` at the pin substitute a local discriminant
//! by each constructor, while retaining an inaccessible copy of the original local. The
//! ordinary elimination engine builds exactly that dependent motive here. Source metadata
//! restores alternative order; it never changes which constructors must be proved.
use super::*;
use crate::source::matching::split_info;

pub(super) struct MatchPlan {
    discriminant: Typed,
    /// The selected matcher before its discriminant. A recursor name alone is shared by
    /// unrelated source matches and cannot identify the occurrences to generalize.
    prefix: Expr,
    position: usize,
    recursor: Name,
    constructors: Vec<Name>,
    alternatives: Vec<split_info::Alternative>,
    annotation: KVMap,
}

pub(super) fn has_annotation(env: &fln_env::environment::Environment, expr: &Expr) -> bool {
    let ExprNode::MData { data, expr } = expr.node() else {
        return false;
    };
    let (head, _) = spine(expr);
    let ExprNode::Const { name, .. } = head.node() else {
        return false;
    };
    let Some(ConstantInfo::Rec(recursor)) = env.find(name) else {
        return false;
    };
    split_info::matches_schema_size(data, recursor)
        && data.contains(&split_info::key())
        && is_match(env, expr)
}

fn unsupported() -> NatDefinitionElabError {
    error(TacticError::SplitMatchUnsupported)
}

impl Context {
    pub(super) fn split_match_plan(
        &mut self,
        goal: &ProofGoal,
        subject: &Subject,
        selected: &Expr,
    ) -> Result<MatchPlan, NatDefinitionElabError> {
        let ExprNode::MData { data, expr } = selected.node() else {
            return Err(unsupported());
        };
        let (head, arguments) = spine(expr);
        let ExprNode::Const { name, levels } = head.node() else {
            return Err(unsupported());
        };
        let Some(ConstantInfo::Rec(rec)) = self.txn.env.find(name).cloned() else {
            return Err(unsupported());
        };
        let [family_name] = rec.all.as_slice() else {
            return Err(unsupported());
        };
        let Some(ConstantInfo::Induct(family)) = self.txn.env.find(family_name).cloned() else {
            return Err(unsupported());
        };
        if rec.is_unsafe
            || family.is_unsafe
            || family.num_nested != 0
            || rec.num_motives != 1
            || rec.num_indices != 0
            || family.num_indices != 0
            || rec.num_params != family.num_params
            || rec.all != family.all
            || rec.num_minors as usize != family.ctors.len()
            || rec.rules.len() != family.ctors.len()
            || levels.len() != rec.base.level_params.len()
            || rec
                .rules
                .iter()
                .map(|rule| &rule.ctor)
                .ne(family.ctors.iter())
        {
            return Err(unsupported());
        }
        let alternatives = split_info::decode(data, &rec).ok_or_else(unsupported)?;
        for rule in &rec.rules {
            self.tick()?;
            let Some(ConstantInfo::Ctor(constructor)) = self.txn.env.find(&rule.ctor) else {
                return Err(unsupported());
            };
            if constructor.is_unsafe
                || constructor.induct != *family_name
                || constructor.num_params != family.num_params
                || constructor.num_fields != rule.nfields
                || constructor.base.level_params != family.base.level_params
            {
                return Err(unsupported());
            }
        }
        let position = usize::try_from(rec.num_params)
            .ok()
            .and_then(|parameters| parameters.checked_add(1))
            .and_then(|prefix| prefix.checked_add(rec.num_minors as usize))
            .ok_or_else(unsupported)?;
        let discriminant = self.instantiate(arguments.get(position).ok_or_else(unsupported)?)?;
        if discriminant.has_loose_bvars() {
            return Err(unsupported());
        }
        if let ExprNode::FVar { id } = discriminant.node()
            && goal.lctx.find(id).is_none_or(|local| local.value.is_some())
        {
            // The pin's splitter does not substitute a constructor for a let declaration.
            // Its assigned value must not be forgotten by treating it as an arbitrary input.
            return Err(unsupported());
        }
        let type_ = self.known_type(&discriminant)?.ok_or_else(unsupported)?;
        let prefix = arguments[..position]
            .iter()
            .cloned()
            .fold(head.clone(), Expr::app);
        if let Subject::Hypothesis(local) = subject {
            // The pin does not simplify a reverted binder's type if later binders depend
            // on it. Keep this case typed until its congruence behavior is implemented.
            if local.value.is_some() || self.elimination_reads(&goal.target)?.contains(&local.id) {
                return Err(unsupported());
            }
            for other in goal.lctx.decls() {
                if other.id == local.id {
                    continue;
                }
                if self.elimination_reads(&other.type_)?.contains(&local.id)
                    || other
                        .value
                        .as_ref()
                        .map(|value| self.elimination_reads(value))
                        .transpose()?
                        .is_some_and(|reads| reads.contains(&local.id))
                {
                    return Err(unsupported());
                }
            }
        }
        Ok(MatchPlan {
            discriminant: Typed {
                value: discriminant,
                type_,
            },
            prefix,
            position,
            recursor: name.clone(),
            constructors: family.ctors,
            alternatives,
            annotation: data.clone(),
        })
    }

    pub(super) fn split_apply_match(
        &mut self,
        proof: &mut ProofState<'_>,
        goal: ProofGoal,
        subject: &Subject,
        plan: MatchPlan,
    ) -> Result<(), NatDefinitionElabError> {
        let parent = self
            .goal_tags
            .get(&goal.id)
            .cloned()
            .unwrap_or_else(Name::anonymous);
        let mut fields = HashMap::new();
        for alternative in &plan.alternatives {
            let names = alternative
                .fields
                .iter()
                .map(|name| {
                    if name.is_anonymous() {
                        Ok(Name::anonymous())
                    } else {
                        self.fresh_inaccessible(name)
                    }
                })
                .collect::<Result<Vec<_>, _>>()?;
            fields.insert(alternative.constructor.clone(), names);
        }
        let (goal, major) = self.split_match_discriminant(proof, goal, subject, &plan)?;
        let original = self.fresh_inaccessible(&major.user_name)?;
        self.txn.lctx = goal.lctx.clone();
        let start = proof.work.len();
        self.eliminate_proof_goal_with_indices(
            proof,
            goal.clone(),
            &eliminate::EliminationSyntax::SplitMatch { fields, original },
            false,
            Some(&major.id),
            None,
        )?;
        // Nonindexed ordinary elimination emits one close followed by its constructor goals,
        // in reverse worklist order. Reordering the goals never reorders recursor arguments.
        let mut generated = proof.work.split_off(start);
        if generated.len() != plan.constructors.len() + 1 {
            return Err(unsupported());
        }
        let mut branches = HashMap::new();
        for constructor in &plan.constructors {
            let Some(Work::Goal(mut branch)) = generated.pop() else {
                return Err(unsupported());
            };
            self.txn.lctx = branch.lctx.clone();
            match subject {
                Subject::Target => {
                    let reduced = self.split_reduce_match(&branch.target, &plan)?;
                    self.constrain(&branch.target, &reduced)?;
                    self.flush(false)?;
                    branch.target = reduced;
                }
                Subject::Hypothesis(local) => {
                    let local = branch
                        .lctx
                        .find_by_user_name(&local.user_name)
                        .cloned()
                        .ok_or_else(unsupported)?;
                    let reduced = self.split_reduce_match(&local.type_, &plan)?;
                    self.constrain(&local.type_, &reduced)?;
                    self.flush(false)?;
                    let mut context = LocalContext::new();
                    for other in branch.lctx.decls() {
                        let mut other = other.clone();
                        if other.id == local.id {
                            other.type_ = reduced.clone();
                        }
                        eliminate::add_local(&mut context, &other);
                    }
                    for introduced in &mut branch.introduced {
                        if introduced.id == local.id {
                            introduced.type_ = reduced.clone();
                        }
                    }
                    branch.lctx = context;
                }
            }
            branches.insert(constructor.clone(), branch);
        }
        let Some(close @ Work::Close(..)) = generated.pop() else {
            return Err(unsupported());
        };
        proof.work.push(close);
        for (index, alternative) in plan.alternatives.iter().enumerate().rev() {
            let branch = branches
                .remove(&alternative.constructor)
                .ok_or_else(unsupported)?;
            self.goal_tags.insert(
                branch.id.clone(),
                super::super::super::trace::append_tag(
                    &parent,
                    &Name::str(Name::anonymous(), format!("h_{}", index + 1)),
                ),
            );
            proof.work.push(Work::Goal(branch));
        }
        self.txn.lctx = goal.lctx;
        Ok(())
    }

    /// `generalizeMatchDiscrs` (Lean/Meta/Tactic/Split.lean): generalize a computed
    /// discriminant only in this matcher's applications, retaining `e = x`. Replacing every
    /// occurrence of `e` would also change branch bodies and the other side of an equation.
    /// The shared generalization builder checks the universal statement and specializes it
    /// with `e` and `Eq.refl e`; ordinary elimination then specializes the equation per case.
    fn split_match_discriminant(
        &mut self,
        proof: &mut ProofState<'_>,
        goal: ProofGoal,
        subject: &Subject,
        plan: &MatchPlan,
    ) -> Result<(ProofGoal, LocalDecl), NatDefinitionElabError> {
        if let ExprNode::FVar { id } = plan.discriminant.value.node() {
            let local = goal.lctx.find(id).cloned().ok_or_else(unsupported)?;
            return Ok((goal, local));
        }
        // A selected hypothesis is generalized in a checked telescope, never retyped in
        // place. The caller has already refused forward dependencies on this hypothesis.
        let (goal, reverted) = match subject {
            Subject::Target => (goal, Vec::new()),
            Subject::Hypothesis(local) => {
                self.reverted_proof_goal(proof, goal, HashSet::from([local.id.clone()]))?
            }
        };
        let discriminant_name = self.fresh_inaccessible(&name(&["x"]))?;
        let equation = self.fresh_inaccessible(&name(&["h"]))?;
        let (mut goal, id) = self.generalized_proof_goal_with(
            proof,
            goal,
            discriminant_name,
            Some(equation),
            plan.discriminant.clone(),
            |context, target, expression, marker| {
                context.split_generalize_match(target, plan, expression, marker)
            },
        )?;
        for local in reverted {
            self.introduce_proof_binder(&mut goal, local.user_name)?;
        }
        goal.lctx = self.txn.lctx.clone();
        let major = goal.lctx.find(&id).cloned().ok_or_else(unsupported)?;
        Ok((goal, major))
    }

    fn split_generalize_match(
        &mut self,
        target: &Expr,
        selected: &MatchPlan,
        expression: &Expr,
        marker: &Expr,
    ) -> Result<Expr, NatDefinitionElabError> {
        let prefix = self.instantiate(&selected.prefix)?;
        let mut done = HashMap::<usize, Expr>::new();
        let mut pending = vec![(target.clone(), false)];
        let mut found = false;
        while let Some((expr, exit)) = pending.pop() {
            self.tick()?;
            let key = expr.allocation_identity();
            if done.contains_key(&key) {
                continue;
            }
            let parts = children(&expr);
            if !exit {
                pending.push((expr, true));
                pending.extend(parts.into_iter().map(|part| (part, false)));
                continue;
            }
            let mut moved = false;
            let parts = parts
                .into_iter()
                .map(|part| {
                    let next = done
                        .get(&part.allocation_identity())
                        .expect("split generalization child")
                        .clone();
                    moved |= next.allocation_identity() != part.allocation_identity();
                    next
                })
                .collect();
            let mut value = if moved {
                rebuild(&expr, parts)
            } else {
                expr.clone()
            };
            if let ExprNode::MData { data, expr: inner } = expr.node()
                && data == &selected.annotation
            {
                let (head, arguments) = spine(inner);
                if arguments.get(selected.position) == Some(expression)
                    && arguments[..selected.position]
                        .iter()
                        .cloned()
                        .fold(head, Expr::app)
                        == prefix
                {
                    let ExprNode::MData { expr: inner, .. } = value.node() else {
                        unreachable!("generalizing children preserves metadata");
                    };
                    let (head, mut arguments) = spine(inner);
                    arguments[selected.position] = marker.clone();
                    value = Expr::mdata(data.clone(), arguments.into_iter().fold(head, Expr::app));
                    found = true;
                }
            }
            done.insert(key, value);
        }
        if !found {
            return Err(unsupported());
        }
        done.remove(&target.allocation_identity())
            .ok_or_else(unsupported)
    }

    /// `simpMatchTargetCore`: reduce this matcher where simp congruence reaches. Only admitted
    /// iota and beta/zeta steps are used; ordinary definitions in a branch stay folded. The
    /// resulting goal is checked definitionally before any following tactic can use it.
    fn split_reduce_match(
        &mut self,
        root: &Expr,
        selected: &MatchPlan,
    ) -> Result<Expr, NatDefinitionElabError> {
        let mut current = root.clone();
        for _ in 0..MAX_REDUCTIONS {
            let mut parameters = HashMap::new();
            let mut reaches = HashMap::new();
            let mut done = HashMap::<(usize, Reach), Expr>::new();
            let mut work = vec![(current.clone(), Reach::Simp, false)];
            let mut changed = false;
            while let Some((expr, reach, exit)) = work.pop() {
                self.tick()?;
                let key = (expr.allocation_identity(), reach);
                if done.contains_key(&key) {
                    continue;
                }
                if let ExprNode::MData { data, expr: inner } = expr.node()
                    && data == &selected.annotation
                    && matches!(spine(inner).0.node(), ExprNode::Const { name, .. }
                        if name == &selected.recursor)
                {
                    let reduced =
                        self.whnf_with_transparency(inner, UnificationTransparency::None, false)?;
                    if reduced != *inner {
                        changed = true;
                        done.insert(key, reduced);
                    } else {
                        done.insert(key, expr);
                    }
                    continue;
                }
                let parts = children(&expr);
                if !exit {
                    let plan = self.split_reaches(&expr, reach, &mut parameters)?;
                    work.push((expr, reach, true));
                    for (part, part_reach) in parts.into_iter().zip(&plan) {
                        if let Some(part_reach) = part_reach {
                            work.push((part, *part_reach, false));
                        }
                    }
                    reaches.insert(key, plan);
                    continue;
                }
                let plan = reaches.remove(&key).expect("match reduction traversal");
                let mut moved = false;
                let parts = parts
                    .into_iter()
                    .zip(plan)
                    .map(|(part, reach)| {
                        let value = reach
                            .and_then(|reach| done.get(&(part.allocation_identity(), reach)))
                            .cloned()
                            .unwrap_or_else(|| part.clone());
                        moved |= value.allocation_identity() != part.allocation_identity();
                        value
                    })
                    .collect();
                let value = if moved {
                    self.head_beta(rebuild(&expr, parts))?
                } else {
                    expr
                };
                done.insert(key, value);
            }
            let next = done
                .remove(&(current.allocation_identity(), Reach::Simp))
                .expect("match reduction root");
            if !changed {
                return Ok(next);
            }
            current = next;
        }
        Err(failure(SourceInferenceError::ResourceLimit))
    }
}
