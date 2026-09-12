//! Exhaustive constructor matching lowered to an admitted dependent recursor.
//!
//! The match compiler is untrusted. It neither evaluates the discriminant to
//! choose a branch nor admits any declarations. Every branch remains an actual
//! minor premise in the generated term. Constrained indices may justify omitted
//! constructors only through retained contradiction proofs; supplied impossible
//! alternatives are refused rather than erased. Both checkers validate the term.
use super::*;
use fln_env::constants::ConstantInfo;
use std::collections::{HashMap, HashSet};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MatchError {
    ExpectedInductive,
    UnsupportedFamily,
    UnrefinedIndices,
    UnrefinedIndexPattern,
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
                "elimination requires a supported single family with direct recursion"
            }
            Self::UnrefinedIndices => {
                "indexed elimination currently requires distinct parameter locals as indices"
            }
            Self::UnrefinedIndexPattern => {
                "direct constructor-field indices require index-pattern refinement"
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

#[derive(Clone, Copy)]
pub(super) struct MatchParts<'a> {
    pub(super) discriminant: &'a Syntax,
    alternatives: &'a [Syntax],
}
pub(super) struct MatchPatterns<'a> {
    pub(super) constructors: HashMap<Name, (Vec<Option<Name>>, &'a Syntax)>,
    pub(super) fallback: Option<(Option<Name>, &'a Syntax)>,
}
pub(super) enum MatchStart<'a> {
    Regular(Box<MatchBuild<'a>>),
    Refined(tactics::ProofState<'a>),
}
struct Branch<'a> {
    constructor: fln_env::constants::ConstructorVal,
    fields: Option<Vec<Option<Name>>>,
    whole: Option<Name>,
    syntax: &'a Syntax,
}
struct DirectMatch<'a> {
    syntax: Option<&'a Syntax>,
    whole: Option<Name>,
}
pub(super) struct MatchBuild<'a> {
    direct: Option<DirectMatch<'a>>,
    recursive: bool,
    unrefined_capture: bool,
    saved: LocalContext,
    target: Expr,
    major: Typed,
    family: Name,
    parameters: Vec<Expr>,
    indices: Vec<LocalDecl>,
    generalized: Vec<LocalDecl>,
    motive_obligation: Option<Typed>,
    levels: Vec<Level>,
    recursor: Typed,
    branches: std::collections::VecDeque<Branch<'a>>,
}
pub(super) struct BranchBinders {
    // Old indices whose direct field patterns lack an index-equation witness.
    // A branch may use the fresh constructor fields, but not capture these
    // original locals (including transitively through retained lets/types).
    unrefined: HashSet<FVarId>,
    hypotheses: Vec<(FVarId, FVarId)>,
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
    /// Independent local indices can be generalized without inventing index
    /// equalities. Repeated, fixed and let-bound indices need an equation
    /// refinement compiler, so they are not silently treated as independent.
    pub(super) fn elimination_index_locals(
        &mut self,
        values: &[Expr],
    ) -> Result<Vec<LocalDecl>, NatDefinitionElabError> {
        let mut seen = HashSet::new();
        let mut indices = Vec::new();
        for value in values {
            self.tick()?;
            let value = self.instantiate(value)?;
            let ExprNode::FVar { id } = value.node() else {
                return Err(error(MatchError::UnrefinedIndices));
            };
            let local = self
                .txn
                .lctx
                .find(id)
                .cloned()
                .ok_or_else(|| error(MatchError::UnrefinedIndices))?;
            if local.value.is_some() || !seen.insert(id.clone()) {
                return Err(error(MatchError::UnrefinedIndices));
            }
            indices.push(local);
        }
        Ok(indices)
    }

    pub(super) fn elimination_result_indices(
        &mut self,
        type_: &Expr,
        family: &Name,
        parameters: usize,
        indices: usize,
    ) -> Result<Vec<Expr>, NatDefinitionElabError> {
        let type_ = self.whnf(type_)?;
        let mut head = &type_;
        let mut values = Vec::new();
        while let ExprNode::App { f, a } = head.node() {
            self.tick()?;
            values.push(a.clone());
            head = f;
        }
        if !matches!(head.node(), ExprNode::Const { name, .. } if name == family)
            || values.len() != parameters + indices
        {
            return Err(error(MatchError::UnsupportedFamily));
        }
        values.reverse();
        Ok(values.split_off(parameters))
    }

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

    pub(super) fn match_apply(
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

    fn indexed_match_motive(
        &mut self,
        target: &Expr,
        major: &Typed,
        family_type: &Expr,
        indices: &[LocalDecl],
    ) -> Result<Expr, NatDefinitionElabError> {
        let body = if let ExprNode::FVar { id } = major.value.node() {
            target
                .abstract_fvar(id, 0)
                .map_err(|_| failure(SourceInferenceError::Scope))?
        } else {
            target.clone()
        };
        let mut motive = Expr::lam(
            Name::anonymous(),
            family_type.clone(),
            body,
            BinderInfo::Default,
        );
        for index in indices.iter().rev() {
            self.tick()?;
            motive = Expr::lam(
                index.user_name.clone(),
                self.instantiate(&index.type_)?,
                motive
                    .abstract_fvar(&index.id, 0)
                    .map_err(|_| failure(SourceInferenceError::Scope))?,
                index.binder_info,
            );
        }
        Ok(motive)
    }

    pub(super) fn start_match<'a>(
        &mut self,
        parts: MatchParts<'a>,
        major: Typed,
        expected: Option<Expr>,
    ) -> Result<MatchStart<'a>, NatDefinitionElabError> {
        // Keep the existing direct/index-polymorphic path, including recursive
        // call lowering. Only the precise index-shape refusal selects the
        // equation-refining backend; typing faults and resource stops propagate.
        let recursive = self.is_recursive_match(&major.value);
        let saved = self.clone();
        match self.start_regular_match(parts, major.clone(), expected.clone()) {
            Ok(build) => Ok(MatchStart::Regular(Box::new(build))),
            Err(NatDefinitionElabError::Inference(SourceInferenceError::Match(
                MatchError::UnrefinedIndices | MatchError::UnrefinedIndexPattern,
            ))) if !recursive => {
                let spent = self.txn.budget.heartbeats_consumed;
                *self = saved;
                self.txn.budget.heartbeats_consumed = spent;
                self.start_refined_match(parts, major, expected)
                    .map(MatchStart::Refined)
            }
            Err(error) => Err(error),
        }
    }

    fn start_regular_match<'a>(
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
            || family.num_nested != 0
            || family.all != [name.clone()]
            || parameters.len() != family.num_params as usize + family.num_indices as usize
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
            || rec.num_indices != family.num_indices
            || rec.num_params != family.num_params
            || rec.num_motives != 1
            || rec.num_minors as usize != family.ctors.len()
            || rec.rules.len() != family.ctors.len()
            || rec.all != family.all
            || !(rec.base.level_params == family.base.level_params
                || (rec.base.level_params.len() == levels.len() + 1
                    && rec.base.level_params[1..] == family.base.level_params))
        {
            return Err(error(MatchError::UnsupportedFamily));
        }
        let index_values = parameters.split_off(family.num_params as usize);
        let target = match expected {
            Some(target) => self.instantiate(&target)?,
            None => {
                let sort = self.type_expected()?;
                self.hole(sort)?
            }
        };
        let recursive = self.recursive_match(&major.value);
        // A sole variable/wildcard pattern does not refine any index. Lower it
        // to a checked local binding, retaining the original discriminant type.
        // In particular, `match xs with | _ => xs` must not force `xs` to have
        // every constructor's result type.
        if !recursive && parts.alternatives.len() == 1 {
            let alt = expect_node(
                &parts.alternatives[0],
                &parser_kind(&["Term", "matchAlt"]),
                4,
                "match alternative",
            )?;
            expect_atom(&alt[0], "|", "alternative separator")?;
            if !matches!(&alt[2], Syntax::Atom { val, .. } if val == "=>" || val == "↦") {
                return Err(error(MatchError::InvalidPattern));
            }
            if let [sequence] = expect_null_args(&alt[1], "single pattern sequence")?
                && let [pattern] = expect_null_args(sequence, "single pattern")?
                && let Ok(whole) = pattern_name(pattern)
                && !whole.as_ref().is_some_and(|name| {
                    matches!(self.txn.env.find(name), Some(ConstantInfo::Ctor(_)))
                        || (family.base.name == Name::from_components(["Bool"])
                            && matches!(name.to_display_string().as_str(), "true" | "false"))
                })
            {
                return Ok(MatchBuild {
                    direct: Some(DirectMatch {
                        syntax: Some(&alt[3]),
                        whole,
                    }),
                    recursive,
                    unrefined_capture: false,
                    saved: self.txn.lctx.clone(),
                    target,
                    major: major.clone(),
                    family: name.clone(),
                    parameters,
                    indices: Vec::new(),
                    generalized: Vec::new(),
                    motive_obligation: None,
                    levels: levels.clone(),
                    // Replaced by the checked body before completion.
                    recursor: major,
                    branches: std::collections::VecDeque::new(),
                });
            }
        }
        // A constructor field used verbatim as a result index needs an actual
        // equation connecting it to the caller's index. Without that witness
        // the direct path must reject even valid captures of the original
        // index through a local alias or dependent hypothesis. Select the
        // checked-equation backend before elaborating any branch, so no source
        // expression is dropped or replayed merely because it uses that name.
        // Structural recursive roots keep their dedicated hypothesis lowering.
        if !recursive && self.match_has_field_indices(&family)? {
            return Err(error(MatchError::UnrefinedIndexPattern));
        }
        let indices = self.elimination_index_locals(&index_values)?;
        // Generalizing later parameters must not rescue an ill-typed original
        // index motive (for example a captured P : Vec A n -> Type). Preserve
        // that original lambda as an ordinary checked let obligation. Its type
        // reconstruction is untrusted; both final checking engines check the
        // lambda's actual applications, including an unused ill-typed value.
        let motive_obligation = if indices.is_empty() {
            None
        } else {
            let value = self.indexed_match_motive(&target, &major, &family_type, &indices)?;
            let type_ = self
                .known_type(&value)?
                .ok_or_else(|| error(MatchError::UnsupportedFamily))?;
            Some(Typed { value, type_ })
        };
        let mut generalized = Vec::new();
        if recursive {
            self.recursive_indices(name, &parameters, &indices)?;
        } else if !indices.is_empty() {
            let mut dependencies: HashSet<_> =
                indices.iter().map(|index| index.id.clone()).collect();
            // Parameters stay fixed. Index domains, however, form a telescope:
            // a later domain may refer to preceding indices. Closing the motive
            // in family order captures those dependencies without inventing an
            // equality between a fixed expression and a constructor result.
            for value in &parameters {
                if !self.elimination_reads(value)?.is_disjoint(&dependencies) {
                    return Err(error(MatchError::UnrefinedIndices));
                }
            }
            let mut preceding = HashSet::new();
            for index in &indices {
                if self
                    .elimination_reads(&index.type_)?
                    .iter()
                    .any(|id| dependencies.contains(id) && !preceding.contains(id))
                {
                    return Err(error(MatchError::UnrefinedIndices));
                }
                preceding.insert(index.id.clone());
            }
            let major_id = if let ExprNode::FVar { id } = major.value.node() {
                dependencies.insert(id.clone());
                Some(id)
            } else {
                None
            };
            for local in self.txn.lctx.clone().decls() {
                if local.value.is_none()
                    && local.binder_info != BinderInfo::InstImplicit
                    && major_id != Some(&local.id)
                    && !indices.iter().any(|index| index.id == local.id)
                    && !self
                        .elimination_reads(&local.type_)?
                        .is_disjoint(&dependencies)
                {
                    dependencies.insert(local.id.clone());
                    generalized.push(local.clone());
                }
            }
        }
        let mut motive_target = if recursive {
            self.recursive_target(&target)?
        } else {
            target.clone()
        };
        for local in generalized.iter().rev() {
            self.tick()?;
            motive_target = Expr::forall_e(
                local.user_name.clone(),
                self.instantiate(&local.type_)?,
                motive_target
                    .abstract_fvar(&local.id, 0)
                    .map_err(|_| failure(SourceInferenceError::Scope))?,
                local.binder_info,
            );
        }
        let target_type = self
            .known_type(&motive_target)?
            .ok_or_else(|| error(MatchError::ExpectedInductive))?;
        let universe = self.sort_level(&Typed {
            value: motive_target.clone(),
            type_: target_type,
        })?;
        let motive = self.indexed_match_motive(&motive_target, &major, &family_type, &indices)?;
        let motive_type = self
            .known_type(&motive)?
            .ok_or_else(|| error(MatchError::ExpectedInductive))?;
        let mut rec_levels = if rec.base.level_params == family.base.level_params {
            Vec::new()
        } else {
            vec![universe]
        };
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
        let MatchPatterns {
            constructors: mut patterns,
            fallback,
        } = self.match_patterns(parts, name, &family.ctors)?;
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
            direct: None,
            recursive,
            unrefined_capture: false,
            saved: self.txn.lctx.clone(),
            target,
            major,
            family: name.clone(),
            parameters,
            indices,
            generalized,
            motive_obligation,
            levels: levels.clone(),
            recursor,
            branches,
        })
    }

    /// One pattern parser serves ordinary and equation-refining matches. Syntax
    /// is borrowed from the original source; no generated tactic script or
    /// reparsing can erase a branch's annotations, references, or provenance.
    /// Read only admitted constructor signatures. A bound result index in the
    /// innermost field slots denotes a field, while the higher slots are fixed
    /// parameters. Compound indices are not assumed injective by this test.
    pub(super) fn match_has_field_indices(
        &mut self,
        family: &fln_env::constants::InductiveVal,
    ) -> Result<bool, NatDefinitionElabError> {
        if family.num_indices == 0 {
            return Ok(false);
        }
        for name in &family.ctors {
            self.tick()?;
            let Some(ConstantInfo::Ctor(constructor)) = self.txn.env.find(name).cloned() else {
                return Err(error(MatchError::UnsupportedFamily));
            };
            if constructor.induct != family.base.name || constructor.num_params != family.num_params
            {
                return Err(error(MatchError::UnsupportedFamily));
            }
            let mut result = &constructor.base.type_;
            for _ in 0..u64::from(constructor.num_params) + u64::from(constructor.num_fields) {
                self.tick()?;
                let ExprNode::ForallE { body, .. } = result.node() else {
                    return Err(error(MatchError::UnsupportedFamily));
                };
                result = body;
            }
            for _ in 0..family.num_indices {
                self.tick()?;
                let ExprNode::App { f, a } = result.node() else {
                    return Err(error(MatchError::UnsupportedFamily));
                };
                if matches!(a.node(), ExprNode::BVar { idx } if *idx < constructor.num_fields) {
                    return Ok(true);
                }
                result = f;
            }
        }
        Ok(false)
    }

    pub(super) fn match_patterns<'a>(
        &mut self,
        parts: MatchParts<'a>,
        name: &Name,
        constructors: &[Name],
    ) -> Result<MatchPatterns<'a>, NatDefinitionElabError> {
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
                if !constructors.contains(&constructor_name) {
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
        if fallback.is_some() && patterns.len() == constructors.len() {
            return Err(error(MatchError::DuplicateConstructor));
        }
        Ok(MatchPatterns {
            constructors: patterns,
            fallback,
        })
    }

    pub(super) fn direct_match_field(
        &mut self,
        domain: &Expr,
        family_type: &Expr,
        name: &Name,
    ) -> Result<bool, NatDefinitionElabError> {
        let domain = self.whnf(domain)?;
        if domain == *family_type {
            return Ok(true);
        }
        if let Some(ConstantInfo::Induct(family)) = self.txn.env.find(name)
            && family.num_indices > 0
        {
            let count = family.num_indices as usize;
            let mut actual = &domain;
            let mut expected = family_type;
            let mut complete = true;
            for _ in 0..count {
                self.tick()?;
                match (actual.node(), expected.node()) {
                    (ExprNode::App { f: a, .. }, ExprNode::App { f: b, .. }) => {
                        actual = a;
                        expected = b;
                    }
                    _ => {
                        complete = false;
                        break;
                    }
                }
            }
            // The admitted constructor/recursor owns positivity and index
            // typing. Here only the fixed family prefix must match; the child
            // may live at different indices from the outer discriminant.
            if complete && actual == expected {
                return Ok(true);
            }
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
        if let Some(direct) = &mut state.direct {
            let Some(syntax) = direct.syntax.take() else {
                return Ok(MatchStep::Complete(
                    self.finish_term(state.recursor.clone(), Some(&state.target))?,
                ));
            };
            // Bind even a wildcard: the original value and its type remain in
            // the core term, so an unused malformed argument cannot disappear.
            let id = FVarId(self.fresh_name()?);
            self.txn.lctx.add_let(
                id.clone(),
                direct.whole.clone().unwrap_or_else(Name::anonymous),
                state.major.type_.clone(),
                state.major.value.clone(),
            );
            return Ok(MatchStep::Branch {
                syntax,
                expected: state.target.clone(),
                binders: BranchBinders {
                    unrefined: HashSet::new(),
                    hypotheses: Vec::new(),
                    locals: vec![self.txn.lctx.find(&id).expect("whole-match binder").clone()],
                    type_: state.target.clone(),
                },
            });
        }
        let Some(branch) = state.branches.pop_front() else {
            if state.unrefined_capture {
                return Err(error(MatchError::UnrefinedIndexPattern));
            }
            let mut result = state.recursor.clone();
            for index in &state.indices {
                result = self.match_apply(
                    result,
                    Typed {
                        value: Expr::fvar(index.id.clone()),
                        type_: index.type_.clone(),
                    },
                )?;
            }
            result = self.match_apply(result, state.major.clone())?;
            for local in &state.generalized {
                let type_ = self.instantiate(&local.type_)?;
                result = self.match_apply(
                    result,
                    Typed {
                        value: Expr::fvar(local.id.clone()),
                        type_,
                    },
                )?;
            }
            if state.recursive {
                for argument in self.recursive_arguments() {
                    let type_ = self
                        .known_type(&argument)?
                        .ok_or_else(|| error(MatchError::UnsupportedFamily))?;
                    result = self.match_apply(
                        result,
                        Typed {
                            value: argument,
                            type_,
                        },
                    )?;
                }
            }
            if let Some(obligation) = &state.motive_obligation {
                result.value = Expr::let_e(
                    Name::anonymous(),
                    obligation.type_.clone(),
                    obligation.value.clone(),
                    result.value,
                    false,
                );
            }
            return Ok(MatchStep::Complete(
                self.finish_term(result, Some(&state.target))?,
            ));
        };
        if state.recursive {
            self.recursive_branch_context()?;
        }
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
        let mut recursive_fields = Vec::new();
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
            let recursive_field =
                self.direct_match_field(binder_type, &family_type, &state.family)?;
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
            if recursive_field {
                recursive_fields.push(id.clone());
            }
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
        let mut unrefined = HashSet::new();
        if !state.indices.is_empty() {
            let constructor_type = self
                .known_type(&constructor)?
                .ok_or_else(|| error(MatchError::UnsupportedFamily))?;
            for (original, index) in state.indices.iter().zip(self.elimination_result_indices(
                &constructor_type,
                &state.family,
                state.parameters.len(),
                state.indices.len(),
            )?) {
                let index = self.whnf(&index)?;
                // No equation relates this fresh field to the outer index.
                // Preserve that boundary by checking what the elaborated branch
                // actually captures, instead of refusing every branch of the
                // family (which also blocked correctly refined recursion).
                if let ExprNode::FVar { id } = index.node()
                    && locals.iter().any(|local| &local.id == id)
                {
                    unrefined.insert(original.id.clone());
                }
            }
        }
        // Recursion hypotheses are actual recursor arguments, but ordinary
        // match syntax does not expose them as names to its branch program.
        let mut hypotheses = Vec::new();
        for field in recursive_fields {
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
            hypotheses.push((field, id.clone()));
            locals.push(LocalDecl {
                id: id.clone(),
                user_name: Name::anonymous(),
                type_: binder_type.clone(),
                value: None,
                binder_info: *binder_info,
                index: self.txn.lctx.len(),
            });
            target = self.substitute(body, &Expr::fvar(id))?;
        }
        if state.recursive {
            let constructor_type = self
                .known_type(&constructor)?
                .ok_or_else(|| error(MatchError::UnsupportedFamily))?;
            self.recursive_index_aliases(&mut locals, &constructor_type)?;
            self.recursive_major_alias(&mut locals, &constructor, &constructor_type)?;
        }
        if let Some(whole) = branch.whole {
            let id = FVarId(self.fresh_name()?);
            let type_ = self
                .known_type(&constructor)?
                .ok_or_else(|| error(MatchError::UnsupportedFamily))?;
            self.txn.lctx.add_let(id.clone(), whole, type_, constructor);
            locals.push(
                self.txn
                    .lctx
                    .find(&id)
                    .expect("whole-pattern binder")
                    .clone(),
            );
        }
        for local in &state.generalized {
            self.tick()?;
            target = self.whnf(&target)?;
            let ExprNode::ForallE {
                binder_type,
                body,
                binder_info,
                ..
            } = target.node()
            else {
                return Err(error(MatchError::UnsupportedFamily));
            };
            let name = if locals
                .iter()
                .any(|binder| binder.user_name == local.user_name)
            {
                Name::anonymous()
            } else {
                local.user_name.clone()
            };
            let id = FVarId(self.fresh_name()?);
            self.txn
                .lctx
                .add_param(id.clone(), name, binder_type.clone(), *binder_info);
            locals.push(
                self.txn
                    .lctx
                    .find(&id)
                    .expect("generalized match binder")
                    .clone(),
            );
            target = self.substitute(body, &Expr::fvar(id))?;
        }
        if state.recursive {
            target = self.recursive_parameters(&mut locals, target)?;
        }
        let expected = self.whnf(&target)?;
        // Fresh generalized parameters shadow their old source names. Clear
        // the old locals only when no retained type or let value needs them;
        // otherwise a captured let would lose its actual free-variable scope.
        // In particular, obsolete dictionaries must not stay searchable merely
        // because their replacement was given the same name.
        if !state.generalized.is_empty() {
            let candidates: HashSet<_> = state
                .generalized
                .iter()
                .map(|local| local.id.clone())
                .collect();
            let context = self.txn.lctx.clone();
            let target_reads = self.elimination_reads(&expected)?;
            let mut reads = Vec::new();
            for local in context.decls() {
                let mut dependencies = self.elimination_reads(&local.type_)?;
                if let Some(value) = &local.value {
                    dependencies.extend(self.elimination_reads(value)?);
                }
                reads.push(dependencies);
            }
            let mut retained = vec![true; context.len()];
            for (index, local) in context.decls().iter().enumerate().rev() {
                self.tick()?;
                if !candidates.contains(&local.id) || target_reads.contains(&local.id) {
                    continue;
                }
                let mut needed = false;
                for (other, dependencies) in reads.iter().enumerate() {
                    self.tick()?;
                    if other != index && retained[other] && dependencies.contains(&local.id) {
                        needed = true;
                        break;
                    }
                }
                if !needed {
                    retained[index] = false;
                }
            }
            self.txn.lctx = LocalContext::new();
            for (local, keep) in context.decls().iter().zip(retained) {
                if keep {
                    if let Some(value) = &local.value {
                        self.txn.lctx.add_let(
                            local.id.clone(),
                            local.user_name.clone(),
                            local.type_.clone(),
                            value.clone(),
                        );
                    } else {
                        self.txn.lctx.add_param(
                            local.id.clone(),
                            local.user_name.clone(),
                            local.type_.clone(),
                            local.binder_info,
                        );
                    }
                }
            }
        }
        Ok(MatchStep::Branch {
            syntax: branch.syntax,
            expected,
            binders: BranchBinders {
                unrefined,
                hypotheses,
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
        if state.recursive {
            value = self.lower_recursive_calls(&value, &binders.hypotheses)?;
        }
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
        if !binders.unrefined.is_empty() {
            let mut pending: Vec<_> = self.elimination_reads(&value)?.into_iter().collect();
            let mut seen = HashSet::new();
            while let Some(id) = pending.pop() {
                self.tick()?;
                if !seen.insert(id.clone()) {
                    continue;
                }
                if binders.unrefined.contains(&id) {
                    // Finish the other branches first. An actual unresolved
                    // self-reference there must still select the existing
                    // recursive elaboration retry, which rebinds the indices.
                    // A nonrecursive match still refuses before completion.
                    state.unrefined_capture = true;
                    break;
                }
                if let Some(local) = state.saved.find(&id) {
                    pending.extend(self.elimination_reads(&local.type_)?);
                    if let Some(value) = &local.value {
                        pending.extend(self.elimination_reads(value)?);
                    }
                }
            }
        }
        self.txn.lctx = state.saved.clone();
        if state.direct.is_some() {
            state.recursor = Typed {
                value,
                type_: binders.type_,
            };
            return Ok(());
        }
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
