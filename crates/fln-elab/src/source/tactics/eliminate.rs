//! Native dependent case analysis and induction through admitted recursors.
//!
//! Goals and branches remain ordinary proof obligations. The original local and
//! its dependency cone are removed before opening branches; dependent hypotheses
//! are generalized in the motive and specialized back in each branch. Only
//! induction exposes recursive hypotheses to tactics or instance search.
use super::*;
use fln_env::constants::{ConstantInfo, ConstructorVal};
use std::collections::{HashMap, HashSet};

#[derive(Clone, Copy)]
enum AlternativeBody<'a> {
    Script(&'a Syntax),
    Term(&'a Syntax),
}
struct Alternative<'a> {
    names: Vec<Name>,
    body: AlternativeBody<'a>,
    explicit_fields: bool,
    exact_fields: bool,
    whole: Option<Name>,
}
pub(super) enum EliminationSyntax<'a> {
    Tactic(&'a [Syntax]),
    Match(matching::MatchParts<'a>),
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
pub(super) fn add_local(context: &mut LocalContext, local: &LocalDecl) {
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
    pub(super) fn specialize_locals(
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
        alternative: Option<&Alternative<'_>>,
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
        let names = alternative.map_or(&[][..], |alt| alt.names.as_slice());
        let explicit_fields = alternative.is_some_and(|alt| alt.explicit_fields);
        let exact_fields = alternative.is_some_and(|alt| alt.exact_fields);
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
            let consumes_name = !explicit_fields
                || matches!(
                    self.whnf(&branch.target)?.node(),
                    ExprNode::ForallE {
                        binder_info: BinderInfo::Default,
                        ..
                    }
                );
            let name = if consumes_name {
                if exact_fields && used >= names.len() {
                    return Err(error(TacticError::EliminationArity));
                }
                let name = names.get(used).cloned().unwrap_or_else(Name::anonymous);
                used += 1;
                name
            } else {
                Name::anonymous()
            };
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
        replacements.push((major.id.clone(), ctor.clone()));
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
        if let Some(whole) = alternative.and_then(|alt| alt.whole.as_ref()) {
            let local = LocalDecl {
                id: FVarId(self.fresh_name()?),
                user_name: whole.clone(),
                type_: ctor_type,
                value: Some(ctor),
                binder_info: BinderInfo::Default,
                index: self.txn.lctx.len(),
            };
            add_local(&mut self.txn.lctx, &local);
            branch.introduced.push(local);
        }
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
        self.eliminate_proof_goal_with_indices(
            proof,
            goal,
            &EliminationSyntax::Tactic(args),
            induction,
            None,
            None,
        )
    }

    /// Source matches use the same checked branch-equation backend as `cases`,
    /// but return their original term syntax to the outer iterative elaborator.
    /// Bind every discriminant, even an ignored expression, in the final term.
    pub(in crate::source) fn start_refined_match<'a>(
        &mut self,
        parts: matching::MatchParts<'a>,
        major: Typed,
        expected: Option<Expr>,
    ) -> Result<ProofState<'a>, NatDefinitionElabError> {
        let saved = self.txn.lctx.clone();
        let target = match expected {
            Some(expected) => self.instantiate(&expected)?,
            None => {
                let sort = self.type_expected()?;
                self.hole(sort)?
            }
        };
        let (root, mut goal) = self.proof_goal(target.clone())?;
        let local = LocalDecl {
            id: FVarId(self.fresh_name()?),
            user_name: Name::anonymous(),
            type_: major.type_,
            value: Some(major.value),
            binder_info: BinderInfo::Default,
            index: self.txn.lctx.len(),
        };
        add_local(&mut self.txn.lctx, &local);
        goal.lctx = self.txn.lctx.clone();
        goal.introduced.push(local.clone());
        let mut proof = ProofState {
            saved,
            target,
            root,
            instructions: Vec::new(),
            cursor: 0,
            work: Vec::new(),
        };
        self.eliminate_proof_goal_with_indices(
            &mut proof,
            goal,
            &EliminationSyntax::Match(parts),
            false,
            Some(&local.id),
            None,
        )?;
        Ok(proof)
    }

    pub(super) fn eliminate_proof_goal_with_indices<'a>(
        &mut self,
        proof: &mut ProofState<'a>,
        goal: ProofGoal,
        input: &EliminationSyntax<'a>,
        induction: bool,
        selected: Option<&FVarId>,
        equations: Option<&index_equations::IndexEquations>,
    ) -> Result<(), NatDefinitionElabError> {
        let (target_name, explicit, scoped, rows) = match input {
            EliminationSyntax::Tactic(args) => {
                let [keyword, target, generalizing, with, alternatives] = *args else {
                    return Err(error(TacticError::MalformedScript));
                };
                expect_atom(
                    keyword,
                    if induction { "induction" } else { "cases" },
                    "elimination tactic",
                )?;
                let Syntax::Ident { val, .. } = target else {
                    return Err(error(TacticError::MalformedScript));
                };
                let rows = expect_null_args(alternatives, "elimination alternatives")?;
                let scoped = match expect_null_args(with, "elimination with")? {
                    [] if rows.is_empty() => false,
                    [keyword] => {
                        expect_atom(keyword, "with", "elimination alternatives")?;
                        true
                    }
                    _ => return Err(error(TacticError::MalformedScript)),
                };
                (
                    val.clone(),
                    expect_null_args(generalizing, "generalized locals")?,
                    scoped,
                    rows,
                )
            }
            EliminationSyntax::Match(_) => (Name::anonymous(), &[][..], true, &[][..]),
        };
        self.resolve_instances(false)?;
        self.flush(false)?;
        let major = selected
            .and_then(|id| self.txn.lctx.find(id))
            .or_else(|| self.txn.lctx.find_by_user_name(&target_name))
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
        let indices = match self.elimination_index_locals(&index_values) {
            Ok(indices) => indices,
            Err(NatDefinitionElabError::Inference(SourceInferenceError::Match(
                matching::MatchError::UnrefinedIndices,
            ))) if equations.is_none() => {
                return self.eliminate_constrained_indices(
                    proof,
                    goal,
                    input,
                    induction,
                    &major,
                    &family,
                    levels,
                    &parameters,
                    &index_values,
                );
            }
            Err(error) => return Err(error),
        };
        let index_ids: HashSet<_> = indices.iter().map(|local| local.id.clone()).collect();
        if equations.is_none() {
            if matches!(input, EliminationSyntax::Match(_))
                && self.match_has_field_indices(&family)?
            {
                return self.eliminate_constrained_indices(
                    proof,
                    goal,
                    input,
                    induction,
                    &major,
                    &family,
                    levels,
                    &parameters,
                    &index_values,
                );
            }
            for parameter in &parameters {
                if !self.elimination_reads(parameter)?.is_disjoint(&index_ids) {
                    return self.eliminate_constrained_indices(
                        proof,
                        goal,
                        input,
                        induction,
                        &major,
                        &family,
                        levels,
                        &parameters,
                        &index_values,
                    );
                }
            }
        }
        let mut removed = HashSet::from([major.id.clone()]);
        removed.extend(index_ids.iter().cloned());
        if let Some(original) = equations.and_then(|plan| plan.induction_major.as_ref()) {
            removed.insert(original.clone());
        }
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

        let mut scripts = HashMap::new();
        let mut fallback = None;
        if let EliminationSyntax::Match(parts) = input {
            let patterns = self.match_patterns(*parts, name, &family.ctors)?;
            for (ctor, (fields, syntax)) in patterns.constructors {
                scripts.insert(
                    ctor,
                    Alternative {
                        names: fields
                            .into_iter()
                            .map(|name| name.unwrap_or_else(Name::anonymous))
                            .collect(),
                        body: AlternativeBody::Term(syntax),
                        explicit_fields: true,
                        exact_fields: true,
                        whole: None,
                    },
                );
            }
            fallback = patterns.fallback.map(|(whole, syntax)| Alternative {
                names: Vec::new(),
                body: AlternativeBody::Term(syntax),
                explicit_fields: true,
                exact_fields: false,
                whole,
            });
        }
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
                        body: AlternativeBody::Script(&fields[4]),
                        explicit_fields: false,
                        exact_fields: false,
                        whole: None,
                    },
                )
                .is_some()
            {
                return Err(error(TacticError::EliminationCoverage));
            }
        }
        if scoped
            && equations.is_none()
            && fallback.is_none()
            && scripts.len() != family.ctors.len()
        {
            return Err(error(TacticError::EliminationCoverage));
        }
        let mut branches = Vec::new();
        let mut fallback_used = false;
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
            let alternative = script.as_ref().or(fallback.as_ref());
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
                alternative,
            )?;
            let work_start = proof.work.len();
            let branch = if let Some(equations) = equations {
                self.refine_index_branch(proof, branch, &equations.names)?
            } else {
                Some(branch)
            };
            if let Some(branch) = branch {
                if scoped && alternative.is_none() {
                    return Err(error(TacticError::EliminationCoverage));
                }
                if script.is_none() && fallback.is_some() {
                    fallback_used = true;
                }
                proof.work.push(match alternative.map(|alt| alt.body) {
                    Some(AlternativeBody::Script(syntax)) => {
                        Work::Script(branch, self.proof_instructions(syntax)?)
                    }
                    Some(AlternativeBody::Term(syntax)) => Work::Term(branch, syntax),
                    None => Work::Goal(branch),
                });
            } else if script.is_some() {
                // Do not silently erase an unreachable source body, including
                // its otherwise unobserved annotations or invalid references.
                return Err(error(TacticError::EliminationCoverage));
            }
            branches.push(proof.work.split_off(work_start));
            self.txn.lctx = retained.clone();
            recursor = self.match_apply(
                recursor,
                Typed {
                    value: hole,
                    type_: minor.clone(),
                },
            )?;
        }
        if fallback.is_some() && !fallback_used {
            return Err(failure(SourceInferenceError::Match(
                matching::MatchError::DuplicateConstructor,
            )));
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
        for branch in branches.into_iter().rev() {
            proof.work.extend(branch);
        }
        Ok(())
    }
}
