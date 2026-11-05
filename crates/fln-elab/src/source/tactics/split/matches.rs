//! Constructor-alternative splitters for annotated source matches.
//!
//! `generalizeTargetsEq` and `Cases.unifyEqs?` at the pin substitute a local discriminant
//! by each constructor, while retaining an inaccessible copy of the original local. The
//! ordinary elimination engine builds exactly that dependent motive here. Source metadata
//! restores alternative order; it never changes which constructors must be proved.
use super::*;
use crate::source::matching::split_info;

pub(super) struct MatchPlan {
    major: LocalDecl,
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
        // Computed discriminants need selective generalization at matcher applications, and
        // overlapping patterns need the matcher's exclusion premises. Neither is equivalent
        // to ordinary constructor elimination, so no guessed splitter is used for them.
        let ExprNode::FVar { id } = discriminant.node() else {
            return Err(unsupported());
        };
        let major = goal.lctx.find(id).cloned().ok_or_else(unsupported)?;
        if major.value.is_some() {
            return Err(unsupported());
        }
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
            major,
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
        let original = self.fresh_inaccessible(&plan.major.user_name)?;
        self.txn.lctx = goal.lctx.clone();
        let start = proof.work.len();
        self.eliminate_proof_goal_with_indices(
            proof,
            goal.clone(),
            &eliminate::EliminationSyntax::SplitMatch { fields, original },
            false,
            Some(&plan.major.id),
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
