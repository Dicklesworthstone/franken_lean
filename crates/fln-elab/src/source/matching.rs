//! Exhaustive constructor matching lowered to an admitted dependent recursor.
//!
//! The match compiler is untrusted. It neither evaluates the discriminant to
//! choose a branch nor admits any declarations. Every branch remains an actual
//! minor premise in the generated term, including branches unreachable for a
//! concrete input. K1 and the independent checker validate the final program.
use super::*;
use fln_env::constants::ConstantInfo;
use std::collections::{HashMap, HashSet};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MatchError {
    ExpectedInductive,
    UnsupportedFamily,
    InvalidPattern,
    DuplicateConstructor,
    MissingConstructor,
    WrongArity,
    DuplicateVariable,
}
impl std::fmt::Display for MatchError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::ExpectedInductive => "match discriminant requires a known inductive type",
            Self::UnsupportedFamily => {
                "match requires a single non-indexed family with direct recursion"
            }
            Self::InvalidPattern => {
                "match requires a constructor with variable fields or a final catch-all"
            }
            Self::DuplicateConstructor => "match repeats a constructor or a catch-all",
            Self::MissingConstructor => "match does not cover every constructor",
            Self::WrongArity => "constructor pattern has the wrong number of explicit fields",
            Self::DuplicateVariable => "constructor pattern repeats a variable",
        })
    }
}
fn error(reason: MatchError) -> NatDefinitionElabError {
    failure(SourceInferenceError::Match(reason))
}

pub(super) struct MatchParts<'a> {
    pub(super) discriminant: &'a Syntax,
    alternatives: &'a [Syntax],
}
struct Branch<'a> {
    constructor: fln_env::constants::ConstructorVal,
    fields: Option<Vec<Option<Name>>>,
    whole: Option<Name>,
    syntax: &'a Syntax,
}
pub(super) struct MatchBuild<'a> {
    saved: LocalContext,
    target: Expr,
    major: Typed,
    family: Name,
    parameters: Vec<Expr>,
    levels: Vec<Level>,
    recursor: Typed,
    branches: std::collections::VecDeque<Branch<'a>>,
}
pub(super) struct BranchBinders {
    locals: Vec<LocalDecl>,
    type_: Expr,
}
pub(super) enum MatchStep<'a> {
    Branch {
        syntax: &'a Syntax,
        expected: Expr,
        binders: BranchBinders,
    },
    Complete(Typed),
}

fn pattern_name(syntax: &Syntax) -> Result<Option<Name>, NatDefinitionElabError> {
    if let Syntax::Ident { val, .. } = syntax {
        if val.is_anonymous() || !val.parent().is_anonymous() {
            return Err(error(MatchError::InvalidPattern));
        }
        return Ok(Some(val.clone()));
    }
    let parts = expect_node(
        syntax,
        &parser_kind(&["Term", "hole"]),
        1,
        "wildcard pattern",
    )?;
    expect_atom(&parts[0], "_", "wildcard")?;
    Ok(None)
}
impl Context {
    pub(super) fn match_parts<'a>(
        &mut self,
        syntax: &'a Syntax,
    ) -> Result<MatchParts<'a>, NatDefinitionElabError> {
        let parts = expect_node(
            syntax,
            &parser_kind(&["Term", "match"]),
            6,
            "match expression",
        )?;
        expect_atom(&parts[0], "match", "match keyword")?;
        expect_empty_null(&parts[1], "unsupported generalizing annotation")?;
        expect_empty_null(&parts[2], "unsupported explicit motive")?;
        let [discriminant] = expect_null_args(&parts[3], "single discriminant")? else {
            return Err(error(MatchError::InvalidPattern));
        };
        let discriminant = expect_node(
            discriminant,
            &parser_kind(&["Term", "matchDiscr"]),
            2,
            "discriminant",
        )?;
        expect_empty_null(&discriminant[0], "unsupported pattern equality binder")?;
        expect_atom(&parts[4], "with", "match alternatives keyword")?;
        let alternatives = expect_node(
            &parts[5],
            &parser_kind(&["Term", "matchAlts"]),
            1,
            "match alternatives",
        )?;
        let alternatives = expect_null_args(&alternatives[0], "match alternatives")?;
        if alternatives.is_empty() {
            return Err(error(MatchError::MissingConstructor));
        }
        if alternatives.len() > 256 {
            return Err(failure(SourceInferenceError::ResourceLimit));
        }
        Ok(MatchParts {
            discriminant: &discriminant[1],
            alternatives,
        })
    }

    fn match_apply(
        &mut self,
        mut function: Typed,
        argument: Typed,
    ) -> Result<Typed, NatDefinitionElabError> {
        self.tick()?;
        let type_ = self.whnf(&function.type_)?;
        let ExprNode::ForallE {
            binder_type, body, ..
        } = type_.node()
        else {
            return Err(error(MatchError::UnsupportedFamily));
        };
        self.constrain_type(&argument.type_, binder_type)?;
        function.value = Expr::app(function.value, argument.value.clone());
        function.type_ = self.substitute(body, &argument.value)?;
        Ok(function)
    }

    pub(super) fn start_match<'a>(
        &mut self,
        parts: MatchParts<'a>,
        major: Typed,
        expected: Option<Expr>,
    ) -> Result<MatchBuild<'a>, NatDefinitionElabError> {
        self.resolve_instances(false)?;
        self.flush(false)?;
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
            return Err(error(MatchError::ExpectedInductive));
        };
        let Some(ConstantInfo::Induct(family)) = self.txn.env.find(name).cloned() else {
            return Err(error(MatchError::ExpectedInductive));
        };
        if family.is_unsafe
            || family.num_indices != 0
            || family.num_nested != 0
            || family.all != [name.clone()]
            || parameters.len() != family.num_params as usize
            || levels.len() != family.base.level_params.len()
        {
            return Err(error(MatchError::UnsupportedFamily));
        }
        if family.ctors.len() > 256 {
            return Err(failure(SourceInferenceError::ResourceLimit));
        }
        let recursor_name = Name::str(name.clone(), "rec");
        let Some(ConstantInfo::Rec(rec)) = self.txn.env.find(&recursor_name).cloned() else {
            return Err(error(MatchError::UnsupportedFamily));
        };
        if rec.is_unsafe
            || rec.num_indices != 0
            || rec.num_params != family.num_params
            || rec.num_motives != 1
            || rec.num_minors as usize != family.ctors.len()
            || rec.rules.len() != family.ctors.len()
            || rec.all != family.all
            || rec.base.level_params.len() != levels.len() + 1
            || rec.base.level_params[1..] != family.base.level_params
        {
            return Err(error(MatchError::UnsupportedFamily));
        }
        let target = match expected {
            Some(target) => self.instantiate(&target)?,
            None => {
                let sort = self.type_expected()?;
                self.hole(sort)?
            }
        };
        let target_type = self
            .known_type(&target)?
            .ok_or_else(|| error(MatchError::ExpectedInductive))?;
        let universe = self.sort_level(&Typed {
            value: target.clone(),
            type_: target_type,
        })?;
        // A local discriminant is generalized in the expected result, producing
        // genuinely dependent branches. Other expressions use a constant motive;
        // no equality is fabricated to refine unrelated local hypotheses.
        let body = if let ExprNode::FVar { id } = major.value.node() {
            target
                .abstract_fvar(id, 0)
                .map_err(|_| failure(SourceInferenceError::Scope))?
        } else {
            target.clone()
        };
        let motive = Expr::lam(
            Name::anonymous(),
            family_type.clone(),
            body,
            BinderInfo::Default,
        );
        let motive_type = self
            .known_type(&motive)?
            .ok_or_else(|| error(MatchError::ExpectedInductive))?;
        let mut rec_levels = vec![universe];
        rec_levels.extend(levels.iter().cloned());
        let mut recursor = Typed {
            value: Expr::const_(recursor_name, rec_levels.clone()),
            type_: self.instantiate_params(&rec.base.type_, &rec.base.level_params, &rec_levels)?,
        };
        for parameter in &parameters {
            let type_ = self
                .known_type(parameter)?
                .ok_or_else(|| error(MatchError::ExpectedInductive))?;
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
        let mut patterns = HashMap::new();
        let mut fallback = None;
        for (index, syntax) in parts.alternatives.iter().enumerate() {
            self.tick()?;
            let alt = expect_node(
                syntax,
                &parser_kind(&["Term", "matchAlt"]),
                4,
                "match alternative",
            )?;
            expect_atom(&alt[0], "|", "alternative separator")?;
            if !matches!(&alt[2], Syntax::Atom { val, .. } if val == "=>" || val == "↦") {
                return Err(error(MatchError::InvalidPattern));
            }
            let [sequence] = expect_null_args(&alt[1], "single pattern sequence")? else {
                return Err(error(MatchError::InvalidPattern));
            };
            let [pattern] = expect_null_args(sequence, "single pattern")? else {
                return Err(error(MatchError::InvalidPattern));
            };
            let (head, arguments) = if let Syntax::Node { kind, args, .. } = pattern
                && kind == &parser_kind(&["Term", "app"])
            {
                let [head, args] = args.as_slice() else {
                    return Err(error(MatchError::InvalidPattern));
                };
                (head, expect_null_args(args, "pattern fields")?)
            } else {
                (pattern, &[][..])
            };
            let constructor_name = if let Syntax::Node { kind, .. } = head
                && kind == &parser_kind(&["Term", "dotIdent"])
            {
                let fields = expect_node(head, kind, 2, "relative constructor")?;
                expect_atom(&fields[0], ".", "relative constructor prefix")?;
                let Syntax::Ident { val, .. } = &fields[1] else {
                    return Err(error(MatchError::InvalidPattern));
                };
                Some(name.append_core(val))
            } else if let Syntax::Ident { val, .. } = head {
                let resolved = if name == &Name::from_components(["Bool"])
                    && matches!(val.to_display_string().as_str(), "true" | "false")
                {
                    name.append_core(val)
                } else {
                    val.clone()
                };
                if matches!(self.txn.env.find(&resolved), Some(ConstantInfo::Ctor(_))) {
                    Some(resolved)
                } else {
                    None
                }
            } else {
                None
            };
            if let Some(constructor_name) = constructor_name {
                if !family.ctors.contains(&constructor_name) {
                    return Err(error(MatchError::InvalidPattern));
                }
                let fields = arguments
                    .iter()
                    .map(pattern_name)
                    .collect::<Result<Vec<_>, _>>()?;
                let mut names = HashSet::new();
                if fields
                    .iter()
                    .flatten()
                    .any(|field| !names.insert(field.clone()))
                {
                    return Err(error(MatchError::DuplicateVariable));
                }
                if patterns
                    .insert(constructor_name, (fields, &alt[3]))
                    .is_some()
                {
                    return Err(error(MatchError::DuplicateConstructor));
                }
            } else {
                if !arguments.is_empty()
                    || index + 1 != parts.alternatives.len()
                    || fallback.is_some()
                {
                    return Err(error(MatchError::InvalidPattern));
                }
                fallback = Some((pattern_name(head)?, &alt[3]));
            }
        }
        // Do not silently discard a written branch: even an unreachable bad
        // term must not vanish before checking. Redundant catch-alls are a
        // visible unsupported pattern in this exhaustive, disjoint profile.
        if fallback.is_some() && patterns.len() == family.ctors.len() {
            return Err(error(MatchError::DuplicateConstructor));
        }
        let mut branches = std::collections::VecDeque::new();
        let mut seen = HashSet::new();
        for rule in &rec.rules {
            self.tick()?;
            if !family.ctors.contains(&rule.ctor) || !seen.insert(rule.ctor.clone()) {
                return Err(error(MatchError::UnsupportedFamily));
            }
            let Some(ConstantInfo::Ctor(constructor)) = self.txn.env.find(&rule.ctor).cloned()
            else {
                return Err(error(MatchError::UnsupportedFamily));
            };
            if constructor.induct != *name
                || constructor.is_unsafe
                || constructor.num_params != family.num_params
                || constructor.num_fields != rule.nfields
                || constructor.base.level_params != family.base.level_params
            {
                return Err(error(MatchError::UnsupportedFamily));
            }
            let (fields, whole, syntax) =
                if let Some((fields, syntax)) = patterns.remove(&rule.ctor) {
                    (Some(fields), None, syntax)
                } else if let Some((whole, syntax)) = &fallback {
                    (None, whole.clone(), *syntax)
                } else {
                    return Err(error(MatchError::MissingConstructor));
                };
            branches.push_back(Branch {
                constructor,
                fields,
                whole,
                syntax,
            });
        }
        Ok(MatchBuild {
            saved: self.txn.lctx.clone(),
            target,
            major,
            family: name.clone(),
            parameters,
            levels: levels.clone(),
            recursor,
            branches,
        })
    }

    fn direct_match_field(
        &mut self,
        domain: &Expr,
        family_type: &Expr,
        name: &Name,
    ) -> Result<bool, NatDefinitionElabError> {
        let domain = self.whnf(domain)?;
        if domain == *family_type {
            return Ok(true);
        }
        let mut pending = vec![&domain];
        let mut seen = HashSet::new();
        while let Some(expr) = pending.pop() {
            self.tick()?;
            if !seen.insert(expr.allocation_identity()) {
                continue;
            }
            match expr.node() {
                ExprNode::Const { name: found, .. } if found == name => {
                    return Err(error(MatchError::UnsupportedFamily));
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
        Ok(false)
    }

    pub(super) fn next_match_branch<'a>(
        &mut self,
        state: &mut MatchBuild<'a>,
    ) -> Result<MatchStep<'a>, NatDefinitionElabError> {
        self.txn.lctx = state.saved.clone();
        let Some(branch) = state.branches.pop_front() else {
            let result = self.match_apply(state.recursor.clone(), state.major.clone())?;
            return Ok(MatchStep::Complete(
                self.finish_term(result, Some(&state.target))?,
            ));
        };
        if branch.constructor.num_fields > 256 {
            return Err(failure(SourceInferenceError::ResourceLimit));
        }
        let type_ = self.whnf(&state.recursor.type_)?;
        let ExprNode::ForallE {
            binder_type: minor_type,
            ..
        } = type_.node()
        else {
            return Err(error(MatchError::UnsupportedFamily));
        };
        let mut target = minor_type.clone();
        let mut locals = Vec::new();
        let mut constructor =
            Expr::const_(branch.constructor.base.name.clone(), state.levels.clone());
        for parameter in &state.parameters {
            constructor = Expr::app(constructor, parameter.clone());
        }
        let family_type = self.whnf(&state.major.type_)?;
        let mut hypotheses = 0;
        let mut consumed = 0;
        for _ in 0..branch.constructor.num_fields {
            self.tick()?;
            target = self.whnf(&target)?;
            let ExprNode::ForallE {
                binder_type,
                binder_info,
                body,
                ..
            } = target.node()
            else {
                return Err(error(MatchError::UnsupportedFamily));
            };
            if self.direct_match_field(binder_type, &family_type, &state.family)? {
                hypotheses += 1;
            }
            let name = if *binder_info == BinderInfo::Default {
                if let Some(fields) = &branch.fields {
                    let field = fields
                        .get(consumed)
                        .ok_or_else(|| error(MatchError::WrongArity))?;
                    consumed += 1;
                    field.clone().unwrap_or_else(Name::anonymous)
                } else {
                    Name::anonymous()
                }
            } else {
                Name::anonymous()
            };
            let id = FVarId(self.fresh_name()?);
            self.txn
                .lctx
                .add_param(id.clone(), name, binder_type.clone(), *binder_info);
            locals.push(self.txn.lctx.find(&id).expect("branch binder").clone());
            let argument = Expr::fvar(id);
            constructor = Expr::app(constructor, argument.clone());
            target = self.substitute(body, &argument)?;
        }
        if branch
            .fields
            .as_ref()
            .is_some_and(|fields| fields.len() != consumed)
        {
            return Err(error(MatchError::WrongArity));
        }
        // Recursion hypotheses are actual recursor arguments, but ordinary
        // match syntax does not expose them as names to its branch program.
        for _ in 0..hypotheses {
            self.tick()?;
            target = self.whnf(&target)?;
            let ExprNode::ForallE {
                binder_type,
                binder_info,
                body,
                ..
            } = target.node()
            else {
                return Err(error(MatchError::UnsupportedFamily));
            };
            let id = FVarId(self.fresh_name()?);
            self.txn.lctx.add_param(
                id.clone(),
                Name::anonymous(),
                binder_type.clone(),
                *binder_info,
            );
            locals.push(
                self.txn
                    .lctx
                    .find(&id)
                    .expect("recursive branch binder")
                    .clone(),
            );
            target = self.substitute(body, &Expr::fvar(id))?;
        }
        if let Some(whole) = branch.whole {
            let id = FVarId(self.fresh_name()?);
            self.txn
                .lctx
                .add_let(id.clone(), whole, family_type, constructor);
            locals.push(
                self.txn
                    .lctx
                    .find(&id)
                    .expect("whole-pattern binder")
                    .clone(),
            );
        }
        let expected = self.whnf(&target)?;
        Ok(MatchStep::Branch {
            syntax: branch.syntax,
            expected,
            binders: BranchBinders {
                locals,
                type_: minor_type.clone(),
            },
        })
    }

    pub(super) fn accept_match_branch(
        &mut self,
        state: &mut MatchBuild<'_>,
        binders: BranchBinders,
        branch: Typed,
    ) -> Result<(), NatDefinitionElabError> {
        self.resolve_instances(false)?;
        self.flush(false)?;
        let mut value = self.instantiate(&branch.value)?;
        for local in binders.locals.into_iter().rev() {
            self.tick()?;
            let domain = self.instantiate(&local.type_)?;
            value = value
                .abstract_fvar(&local.id, 0)
                .map_err(|_| failure(SourceInferenceError::Scope))?;
            value = if let Some(local_value) = local.value {
                Expr::let_e(
                    local.user_name,
                    domain,
                    self.instantiate(&local_value)?,
                    value,
                    false,
                )
            } else {
                Expr::lam(local.user_name, domain, value, local.binder_info)
            };
        }
        self.txn.lctx = state.saved.clone();
        state.recursor = self.match_apply(
            state.recursor.clone(),
            Typed {
                value,
                type_: binders.type_,
            },
        )?;
        Ok(())
    }
}
