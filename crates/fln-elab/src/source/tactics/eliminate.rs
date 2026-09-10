//! Native dependent case analysis and induction through admitted recursors.
//!
//! Goals and branches remain ordinary proof obligations. The original local and
//! its dependency cone are removed before opening branches; dependent hypotheses
//! are generalized in the motive and specialized back in each branch. Only
//! induction exposes recursive hypotheses to tactics or instance search.
use super::*;
use fln_env::constants::{ConstantInfo, ConstructorVal};
use std::collections::{HashMap, HashSet};

struct Alternative<'a> {
    names: Vec<Name>,
    script: &'a Syntax,
}
struct EliminationContext<'a> {
    parameters: &'a [Expr],
    levels: &'a [Level],
    major: &'a LocalDecl,
    indices: &'a [LocalDecl],
    original_target: &'a Expr,
    reverted: &'a [LocalDecl],
    induction: bool,
}
fn add_local(context: &mut LocalContext, local: &LocalDecl) {
    if let Some(value) = &local.value {
        context.add_let(
            local.id.clone(),
            local.user_name.clone(),
            local.type_.clone(),
            value.clone(),
        );
    } else {
        context.add_param(
            local.id.clone(),
            local.user_name.clone(),
            local.type_.clone(),
            local.binder_info,
        );
    }
}
impl Context {
    pub(in crate::source) fn elimination_reads(
        &mut self,
        expr: &Expr,
    ) -> Result<HashSet<FVarId>, NatDefinitionElabError> {
        let expr = self.instantiate(expr)?;
        let mut pending = vec![&expr];
        let mut visited = HashSet::new();
        let mut found = HashSet::new();
        while let Some(expr) = pending.pop() {
            self.tick()?;
            if !visited.insert(expr.allocation_identity()) {
                continue;
            }
            match expr.node() {
                ExprNode::FVar { id } => {
                    found.insert(id.clone());
                }
                ExprNode::App { f, a } => {
                    pending.push(a);
                    pending.push(f);
                }
                ExprNode::Lam {
                    binder_type, body, ..
                }
                | ExprNode::ForallE {
                    binder_type, body, ..
                } => {
                    pending.push(body);
                    pending.push(binder_type);
                }
                ExprNode::LetE {
                    type_, value, body, ..
                } => {
                    pending.push(body);
                    pending.push(value);
                    pending.push(type_);
                }
                ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => pending.push(expr),
                _ => {}
            }
        }
        Ok(found)
    }
    fn specialize_locals(
        &mut self,
        expr: &Expr,
        replacements: &[(FVarId, Expr)],
    ) -> Result<Expr, NatDefinitionElabError> {
        let mut value = self.instantiate(expr)?;
        for (id, replacement) in replacements {
            self.tick()?;
            value = value
                .abstract_fvar(id, 0)
                .map_err(|_| failure(SourceInferenceError::Scope))?;
            value = self.substitute(&value, replacement)?;
        }
        Ok(value)
    }
    fn elimination_binder(
        &mut self,
        goal: &mut ProofGoal,
        name: Name,
        visible: bool,
    ) -> Result<LocalDecl, NatDefinitionElabError> {
        let target = self.whnf(&goal.target)?;
        let ExprNode::ForallE {
            binder_type,
            body,
            binder_info,
            ..
        } = target.node()
        else {
            return Err(error(TacticError::UnsupportedEliminator));
        };
        let id = FVarId(self.fresh_name()?);
        let local = LocalDecl {
            id: id.clone(),
            user_name: name,
            type_: binder_type.clone(),
            value: None,
            binder_info: *binder_info,
            index: self.txn.lctx.len(),
        };
        goal.target = self.substitute(body, &Expr::fvar(id))?;
        if visible {
            add_local(&mut self.txn.lctx, &local);
        }
        goal.introduced.push(local.clone());
        Ok(local)
    }
    fn elimination_branch(
        &mut self,
        mut branch: ProofGoal,
        constructor: &ConstructorVal,
        context: &EliminationContext<'_>,
        names: &[Name],
    ) -> Result<ProofGoal, NatDefinitionElabError> {
        let &EliminationContext {
            parameters,
            levels,
            major,
            indices,
            original_target,
            reverted,
            induction,
        } = context;
        let family_type = self.whnf(&major.type_)?;
        let mut ctor = Expr::const_(constructor.base.name.clone(), levels.to_vec());
        for param in parameters {
            self.tick()?;
            ctor = Expr::app(ctor, param.clone());
        }
        let mut used = 0;
        let mut recursive_fields = 0;
        for _ in 0..constructor.num_fields {
            self.tick()?;
            let name = names.get(used).cloned().unwrap_or_else(Name::anonymous);
            used += 1;
            let local = self.elimination_binder(&mut branch, name, true)?;
            if self.direct_match_field(&local.type_, &family_type, &constructor.induct)? {
                recursive_fields += 1;
            }
            ctor = Expr::app(ctor, Expr::fvar(local.id));
        }
        for _ in 0..recursive_fields {
            self.tick()?;
            let name = if induction {
                let name = names.get(used).cloned().unwrap_or_else(Name::anonymous);
                used += 1;
                name
            } else {
                Name::anonymous()
            };
            self.elimination_binder(&mut branch, name, induction)?;
        }
        if names.len() > used {
            return Err(error(TacticError::EliminationArity));
        }
        // Reintroduce the exact dependent telescope, including let definitions.
        // Rebuilding from original declarations avoids whnf erasing those lets.
        let ctor_type = self
            .known_type(&ctor)?
            .ok_or_else(|| error(TacticError::UnsupportedEliminator))?;
        let result_indices = self.elimination_result_indices(
            &ctor_type,
            &constructor.induct,
            parameters.len(),
            indices.len(),
        )?;
        let mut replacements: Vec<_> = indices
            .iter()
            .zip(result_indices)
            .map(|(local, value)| (local.id.clone(), value))
            .collect();
        replacements.push((major.id.clone(), ctor));
        for old in reverted {
            self.tick()?;
            let type_ = self.specialize_locals(&old.type_, &replacements)?;
            let value = old
                .value
                .as_ref()
                .map(|value| self.specialize_locals(value, &replacements))
                .transpose()?;
            let id = FVarId(self.fresh_name()?);
            let name = if names.contains(&old.user_name) {
                Name::anonymous()
            } else {
                old.user_name.clone()
            };
            let local = LocalDecl {
                id: id.clone(),
                user_name: name,
                type_,
                value,
                binder_info: old.binder_info,
                index: self.txn.lctx.len(),
            };
            add_local(&mut self.txn.lctx, &local);
            branch.introduced.push(local);
            replacements.push((old.id.clone(), Expr::fvar(id)));
        }
        branch.target = self.specialize_locals(original_target, &replacements)?;
        branch.lctx = self.txn.lctx.clone();
        Ok(branch)
    }

    pub(super) fn eliminate_proof_goal<'a>(
        &mut self,
        proof: &mut ProofState<'a>,
        goal: ProofGoal,
        args: &'a [Syntax],
        induction: bool,
    ) -> Result<(), NatDefinitionElabError> {
        let [keyword, target, generalizing, with, alternatives] = args else {
            return Err(error(TacticError::MalformedScript));
        };
        expect_atom(
            keyword,
            if induction { "induction" } else { "cases" },
            "elimination tactic",
        )?;
        let Syntax::Ident {
            val: target_name, ..
        } = target
        else {
            return Err(error(TacticError::MalformedScript));
        };
        self.resolve_instances(false)?;
        self.flush(false)?;
        let major = self
            .txn
            .lctx
            .find_by_user_name(target_name)
            .cloned()
            .ok_or_else(|| error(TacticError::EliminationLocal))?;
        let family_type = self.whnf(&major.type_)?;
        let mut head = &family_type;
        let mut parameters = Vec::new();
        while let ExprNode::App { f, a } = head.node() {
            self.tick()?;
            parameters.push(a.clone());
            head = f;
        }
        parameters.reverse();
        let ExprNode::Const { name, levels } = head.node() else {
            return Err(error(TacticError::UnsupportedEliminator));
        };
        let Some(ConstantInfo::Induct(family)) = self.txn.env.find(name).cloned() else {
            return Err(error(TacticError::UnsupportedEliminator));
        };
        let rec_name = Name::str(name.clone(), "rec");
        let Some(ConstantInfo::Rec(rec)) = self.txn.env.find(&rec_name).cloned() else {
            return Err(error(TacticError::UnsupportedEliminator));
        };
        if family.is_unsafe
            || family.num_nested != 0
            || family.all != [name.clone()]
            || parameters.len() != family.num_params as usize + family.num_indices as usize
            || levels.len() != family.base.level_params.len()
            || rec.is_unsafe
            || rec.num_params != family.num_params
            || rec.num_indices != family.num_indices
            || rec.num_motives != 1
            || rec.num_minors as usize != family.ctors.len()
            || rec.rules.len() != family.ctors.len()
            || rec.all != family.all
        {
            return Err(error(TacticError::UnsupportedEliminator));
        }
        if family.ctors.len() > 256 {
            return Err(failure(SourceInferenceError::ResourceLimit));
        }
        let index_values = parameters.split_off(family.num_params as usize);
        let indices = self.elimination_index_locals(&index_values)?;
        let index_ids: HashSet<_> = indices.iter().map(|local| local.id.clone()).collect();
        let mut removed = HashSet::from([major.id.clone()]);
        removed.extend(index_ids.iter().cloned());
        let explicit = expect_null_args(generalizing, "generalized locals")?;
        if !explicit.is_empty() {
            if !induction {
                return Err(error(TacticError::InvalidGeneralization));
            }
            expect_atom(&explicit[0], "generalizing", "generalization keyword")?;
            if explicit.len() == 1 {
                return Err(error(TacticError::InvalidGeneralization));
            }
            for name in &explicit[1..] {
                self.tick()?;
                let Syntax::Ident { val, .. } = name else {
                    return Err(error(TacticError::InvalidGeneralization));
                };
                let local = goal
                    .lctx
                    .find_by_user_name(val)
                    .ok_or_else(|| error(TacticError::InvalidGeneralization))?;
                if !removed.insert(local.id.clone()) {
                    return Err(error(TacticError::InvalidGeneralization));
                }
            }
        }
        // Local contexts are ordered telescopes: one forward pass computes the
        // transitive dependency cone once explicitly generalized locals are known.
        for local in goal.lctx.decls() {
            let mut reads = self.elimination_reads(&local.type_)?;
            if let Some(value) = &local.value {
                reads.extend(self.elimination_reads(value)?);
            }
            if reads.iter().any(|id| removed.contains(id)) {
                removed.insert(local.id.clone());
            }
        }
        if self
            .elimination_reads(&major.type_)?
            .iter()
            .any(|id| removed.contains(id) && !index_ids.contains(id))
        {
            return Err(error(TacticError::InvalidGeneralization));
        }
        for parameter in &parameters {
            if self
                .elimination_reads(parameter)?
                .iter()
                .any(|id| removed.contains(id))
            {
                return Err(error(TacticError::InvalidGeneralization));
            }
        }
        let mut preceding_indices = HashSet::new();
        for index in &indices {
            if self
                .elimination_reads(&index.type_)?
                .iter()
                .any(|id| removed.contains(id) && !preceding_indices.contains(id))
            {
                return Err(error(TacticError::InvalidGeneralization));
            }
            preceding_indices.insert(index.id.clone());
        }
        let reverted: Vec<_> = goal
            .lctx
            .decls()
            .iter()
            .filter(|local| {
                local.id != major.id
                    && !index_ids.contains(&local.id)
                    && removed.contains(&local.id)
            })
            .cloned()
            .collect();
        let mut retained = LocalContext::new();
        for local in goal.lctx.decls() {
            if !removed.contains(&local.id) {
                add_local(&mut retained, local);
            }
        }
        let mut generalized = self.instantiate(&goal.target)?;
        for local in reverted.iter().rev() {
            self.tick()?;
            generalized = generalized
                .abstract_fvar(&local.id, 0)
                .map_err(|_| failure(SourceInferenceError::Scope))?;
            let domain = self.instantiate(&local.type_)?;
            generalized = if let Some(value) = &local.value {
                Expr::let_e(
                    local.user_name.clone(),
                    domain,
                    self.instantiate(value)?,
                    generalized,
                    false,
                )
            } else {
                Expr::forall_e(
                    local.user_name.clone(),
                    domain,
                    generalized,
                    local.binder_info,
                )
            };
        }
        let target_type = self
            .known_type(&generalized)?
            .ok_or_else(|| error(TacticError::UnsupportedEliminator))?;
        let universe = self.sort_level(&Typed {
            value: generalized.clone(),
            type_: target_type,
        })?;
        let mut motive = Expr::lam(
            Name::anonymous(),
            family_type.clone(),
            generalized
                .abstract_fvar(&major.id, 0)
                .map_err(|_| failure(SourceInferenceError::Scope))?,
            BinderInfo::Default,
        );
        for index in indices.iter().rev() {
            self.tick()?;
            let body = motive
                .abstract_fvar(&index.id, 0)
                .map_err(|_| failure(SourceInferenceError::Scope))?;
            motive = Expr::lam(
                index.user_name.clone(),
                self.instantiate(&index.type_)?,
                body,
                index.binder_info,
            );
        }
        let motive_type = self
            .known_type(&motive)?
            .ok_or_else(|| error(TacticError::UnsupportedEliminator))?;
        let rec_levels = if rec.base.level_params == family.base.level_params {
            levels.clone()
        } else if rec.base.level_params.len() == levels.len() + 1
            && rec.base.level_params[1..] == family.base.level_params
        {
            let mut result = vec![universe];
            result.extend(levels.iter().cloned());
            result
        } else {
            return Err(error(TacticError::UnsupportedEliminator));
        };
        let mut recursor = Typed {
            value: Expr::const_(rec_name, rec_levels.clone()),
            type_: self.instantiate_params(&rec.base.type_, &rec.base.level_params, &rec_levels)?,
        };
        for parameter in &parameters {
            let type_ = self
                .known_type(parameter)?
                .ok_or_else(|| error(TacticError::UnsupportedEliminator))?;
            recursor = self.match_apply(
                recursor,
                Typed {
                    value: parameter.clone(),
                    type_,
                },
            )?;
        }
        recursor = self.match_apply(
            recursor,
            Typed {
                value: motive,
                type_: motive_type,
            },
        )?;

        let with = expect_null_args(with, "elimination with")?;
        let rows = expect_null_args(alternatives, "elimination alternatives")?;
        let scoped = match with {
            [] if rows.is_empty() => false,
            [keyword] => {
                expect_atom(keyword, "with", "elimination alternatives")?;
                true
            }
            _ => return Err(error(TacticError::MalformedScript)),
        };
        let mut scripts = HashMap::new();
        for row in rows {
            self.tick()?;
            let fields = expect_node(
                row,
                &parser_kind(&["Tactic", "inductionAlt"]),
                5,
                "elimination alternative",
            )?;
            expect_atom(&fields[0], "|", "elimination alternative")?;
            if !matches!(&fields[3], Syntax::Atom { val, .. } if val == "=>" || val == "↦") {
                return Err(error(TacticError::MalformedScript));
            }
            let Syntax::Ident { val, .. } = &fields[1] else {
                return Err(error(TacticError::MalformedScript));
            };
            let ctor = if family.ctors.contains(val) {
                val.clone()
            } else {
                name.append_core(val)
            };
            if !family.ctors.contains(&ctor) {
                return Err(error(TacticError::EliminationCoverage));
            }
            let mut names = Vec::new();
            let mut unique = HashSet::new();
            for field in expect_null_args(&fields[2], "elimination binders")? {
                self.tick()?;
                let name = match field {
                    Syntax::Ident { val, .. } => val.clone(),
                    Syntax::Atom { val, .. } if val == "_" => Name::anonymous(),
                    _ => return Err(error(TacticError::MalformedScript)),
                };
                if !name.is_anonymous() && !unique.insert(name.clone()) {
                    return Err(error(TacticError::EliminationArity));
                }
                names.push(name);
            }
            if scripts
                .insert(
                    ctor,
                    Alternative {
                        names,
                        script: &fields[4],
                    },
                )
                .is_some()
            {
                return Err(error(TacticError::EliminationCoverage));
            }
        }
        if scoped && scripts.len() != family.ctors.len() {
            return Err(error(TacticError::EliminationCoverage));
        }
        let mut branches = Vec::new();
        let mut seen = HashSet::new();
        for rule in &rec.rules {
            self.tick()?;
            if !family.ctors.contains(&rule.ctor) || !seen.insert(rule.ctor.clone()) {
                return Err(error(TacticError::UnsupportedEliminator));
            }
            let Some(ConstantInfo::Ctor(constructor)) = self.txn.env.find(&rule.ctor).cloned()
            else {
                return Err(error(TacticError::UnsupportedEliminator));
            };
            if constructor.induct != *name
                || constructor.is_unsafe
                || constructor.num_params != family.num_params
                || constructor.base.level_params != family.base.level_params
                || constructor.num_fields != rule.nfields
            {
                return Err(error(TacticError::UnsupportedEliminator));
            }
            let rec_type = self.whnf(&recursor.type_)?;
            let ExprNode::ForallE {
                binder_type: minor, ..
            } = rec_type.node()
            else {
                return Err(error(TacticError::UnsupportedEliminator));
            };
            self.txn.lctx = retained.clone();
            let (hole, branch) = self.proof_goal(minor.clone())?;
            let script = scripts.remove(&rule.ctor);
            let names = script
                .as_ref()
                .map_or(&[][..], |script| script.names.as_slice());
            let branch = self.elimination_branch(
                branch,
                &constructor,
                &EliminationContext {
                    parameters: &parameters,
                    levels,
                    major: &major,
                    indices: &indices,
                    original_target: &goal.target,
                    reverted: &reverted,
                    induction,
                },
                names,
            )?;
            let instructions = script
                .map(|script| self.proof_instructions(script.script))
                .transpose()?;
            branches.push((branch, instructions));
            self.txn.lctx = retained.clone();
            recursor = self.match_apply(
                recursor,
                Typed {
                    value: hole,
                    type_: minor.clone(),
                },
            )?;
        }
        self.txn.lctx = goal.lctx.clone();
        for index in &indices {
            let type_ = self.instantiate(&index.type_)?;
            recursor = self.match_apply(
                recursor,
                Typed {
                    value: Expr::fvar(index.id.clone()),
                    type_,
                },
            )?;
        }
        recursor = self.match_apply(
            recursor,
            Typed {
                value: Expr::fvar(major.id),
                type_: major.type_,
            },
        )?;
        for local in &reverted {
            if local.value.is_none() {
                let type_ = self.instantiate(&local.type_)?;
                recursor = self.match_apply(
                    recursor,
                    Typed {
                        value: Expr::fvar(local.id.clone()),
                        type_,
                    },
                )?;
            }
        }
        proof.work.push(Work::Close(goal, recursor.value));
        for (branch, instructions) in branches.into_iter().rev() {
            proof.work.push(match instructions {
                Some(instructions) => Work::Script(branch, instructions),
                None => Work::Goal(branch),
            });
        }
        Ok(())
    }
}
