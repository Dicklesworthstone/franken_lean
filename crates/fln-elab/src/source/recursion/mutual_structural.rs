//! A recursive component over one family shares one `brecOn`, with a `PProd` motive
//! containing every member's result. This is the same construction as the pin's
//! Structural/BRecOn: recursive calls select a component of the below dictionary,
//! never an unchecked definition or a well-founded substitute.
//!
//! Source bodies are elaborated with that dependent dictionary in scope. Ordinary match
//! elaboration then generalizes it over each constructor, including deeper subterms. The
//! existing canary-motive search identifies an entry by its smaller argument, not by its
//! result type. Every produced declaration still passes the ordinary two-checker batch.
use super::*;
use fln_env::constants::{ConstantInfo, DefinitionSafety};
use std::sync::Arc;

pub(in crate::source) struct StructuralPlan {
    pub name: Name,
    pub names: Vec<Name>,
    pub types: Vec<Expr>,
    pub level_params: Vec<Name>,
    pub arities: Vec<usize>,
    pub fixed: usize,
    family: Name,
    family_parameters: usize,
    /// These terms are lambda-closed over the common fixed prefix.
    domain: Expr,
    recursor: Expr,
    recursor_type: Expr,
    /// Each component is additionally lambda-closed over the common major. Its value is
    /// the Pi type of any remaining, varying arguments followed by that member's result.
    components: Vec<Expr>,
}

#[derive(Clone)]
pub(in crate::source) struct StructuralMember {
    plan: Arc<StructuralPlan>,
    index: usize,
    active: Option<Active>,
    piece: Option<Expr>,
}

#[derive(Clone)]
struct Active {
    fixed: Vec<LocalDecl>,
    below: Name,
    references: Vec<Typed>,
    markers: Vec<FVarId>,
}

impl StructuralMember {
    pub(in crate::source) fn new(plan: Arc<StructuralPlan>, index: usize) -> Self {
        Self {
            plan,
            index,
            active: None,
            piece: None,
        }
    }

    pub(in crate::source) fn piece(&self) -> Option<&Expr> {
        self.piece.as_ref()
    }

    pub(in crate::source) fn target(&self, name: &Name) -> Option<&Typed> {
        let index = self
            .plan
            .names
            .iter()
            .position(|candidate| candidate == name)?;
        self.active.as_ref()?.references.get(index)
    }

    pub(in crate::source) fn hides(&self, local: &LocalDecl) -> bool {
        self.active.as_ref().is_some_and(|active| {
            local.user_name == active.below
                || active.markers.iter().any(|marker| marker == &local.id)
        })
    }
}

fn scope() -> NatDefinitionElabError {
    failure(SourceInferenceError::Scope)
}

fn unsupported(shape: &'static str) -> NatDefinitionElabError {
    error(RecursionError::MutualStructuralUnsupported(shape))
}

fn project(mut value: Expr, index: usize, count: usize) -> Expr {
    let product = Name::from_components(["PProd"]);
    for _ in 0..index {
        value = Expr::proj(product.clone(), 1, value);
    }
    if index + 1 < count {
        value = Expr::proj(product, 0, value);
    }
    value
}

impl Context {
    fn structural_close(
        &mut self,
        expression: &Expr,
        locals: &[LocalDecl],
        lambda: bool,
    ) -> Result<Expr, NatDefinitionElabError> {
        let mut value = self.instantiate(expression)?;
        for local in locals.iter().rev() {
            self.tick()?;
            let body = value.abstract_fvar(&local.id, 0).map_err(|_| scope())?;
            let domain = self.instantiate(&local.type_)?;
            value = if lambda {
                Expr::lam(local.user_name.clone(), domain, body, local.binder_info)
            } else {
                Expr::forall_e(local.user_name.clone(), domain, body, local.binder_info)
            };
        }
        Ok(value)
    }

    fn structural_open(
        &mut self,
        expression: &Expr,
        arguments: &[Expr],
    ) -> Result<Expr, NatDefinitionElabError> {
        let mut value = expression.clone();
        for argument in arguments {
            self.tick()?;
            let ExprNode::Lam { body, .. } = value.node() else {
                return Err(scope());
            };
            value = self.substitute(body, argument)?;
        }
        Ok(value)
    }

    fn structural_fixed_locals(
        &mut self,
        type_: &Expr,
        count: usize,
    ) -> Result<(Vec<LocalDecl>, Expr), NatDefinitionElabError> {
        let mut type_ = type_.clone();
        let mut locals = Vec::new();
        for _ in 0..count {
            self.tick()?;
            let ExprNode::ForallE {
                binder_name,
                binder_type,
                body,
                binder_info,
            } = type_.node()
            else {
                return Err(unsupported("a complete common fixed prefix"));
            };
            let id = FVarId(self.fresh_name()?);
            let local = self
                .txn
                .lctx
                .add_param(
                    id.clone(),
                    binder_name.clone(),
                    binder_type.clone(),
                    *binder_info,
                )
                .clone();
            locals.push(local);
            type_ = self.substitute(body, &Expr::fvar(id))?;
        }
        Ok((locals, type_))
    }

    fn structural_pair_type(
        &mut self,
        left: Expr,
        right: Expr,
    ) -> Result<Expr, NatDefinitionElabError> {
        let product = self.constant(&Name::from_components(["PProd"]))?;
        let product = self.course_apply(product, left)?;
        Ok(self.course_apply(product, right)?.value)
    }

    fn structural_pair(
        &mut self,
        left: Typed,
        right: Typed,
    ) -> Result<Typed, NatDefinitionElabError> {
        let constructor = self.constant(&Name::from_components(["PProd", "mk"]))?;
        let constructor = self.course_apply(constructor, left.type_.clone())?;
        let constructor = self.course_apply(constructor, right.type_.clone())?;
        let constructor = self.match_apply(constructor, left)?;
        self.match_apply(constructor, right)
    }

    /// Construct a shared motive over a nonindexed, nonmutual inductive family. The
    /// decreasing argument follows the common fixed prefix; every later argument varies.
    /// Component result types and arities may differ, including dependent trailing binders.
    pub(in crate::source) fn mutual_structural_plan(
        &mut self,
        names: Vec<Name>,
        types: Vec<Expr>,
        arities: Vec<usize>,
        fixed: usize,
        level_params: Vec<Name>,
    ) -> Result<StructuralPlan, NatDefinitionElabError> {
        if names.is_empty()
            || types.len() != names.len()
            || arities.len() != names.len()
            || arities.iter().any(|arity| *arity <= fixed)
        {
            return Err(unsupported("a decreasing argument in every member"));
        }
        self.level_params = level_params.clone();
        self.explicit_levels = level_params.len();
        let saved = self.txn.lctx.clone();
        let result = (|| {
            let (fixed_locals, first) = self.structural_fixed_locals(&types[0], fixed)?;
            let ExprNode::ForallE {
                binder_type: domain,
                binder_info,
                ..
            } = first.node()
            else {
                return Err(unsupported("an explicit structural argument"));
            };
            if *binder_info != BinderInfo::Default {
                return Err(unsupported("an explicit structural argument"));
            }
            let domain = self.whnf(domain)?;
            let (head, parameters) = self.course_spine(&domain)?;
            let ExprNode::Const {
                name: family_name,
                levels,
            } = head.node()
            else {
                return Err(unsupported("one inductive family after the fixed prefix"));
            };
            let Some(ConstantInfo::Induct(family)) = self.txn.env.find(family_name).cloned() else {
                return Err(unsupported("one inductive family after the fixed prefix"));
            };
            if family.all.len() != 1
                || family.num_indices != 0
                || parameters.len() != family.num_params as usize
            {
                return Err(unsupported("a nonindexed, nonmutual inductive family"));
            }
            let brec = Name::str(family_name.clone(), "brecOn");
            if !self.is_auxiliary_recursor(&brec)? {
                return Err(unsupported("an admitted course-of-values recursor"));
            }
            let Some(ConstantInfo::Defn(definition)) = self.txn.env.find(&brec).cloned() else {
                return Err(unsupported("an admitted course-of-values recursor"));
            };
            if definition.safety != DefinitionSafety::Safe {
                return Err(unsupported("a safe course-of-values recursor"));
            }
            let major_id = FVarId(self.fresh_name()?);
            let major = self
                .txn
                .lctx
                .add_param(
                    major_id,
                    Name::anonymous(),
                    domain.clone(),
                    BinderInfo::Default,
                )
                .clone();
            let mut components = Vec::new();
            for type_ in &types {
                let mut remainder = type_.clone();
                for local in &fixed_locals {
                    self.tick()?;
                    let ExprNode::ForallE {
                        binder_type, body, ..
                    } = remainder.node()
                    else {
                        return Err(unsupported("one common fixed prefix"));
                    };
                    if !self.defeq_guarded(binder_type, &local.type_)? {
                        return Err(unsupported("fixed parameters of the same type"));
                    }
                    remainder = self.substitute(body, &Expr::fvar(local.id.clone()))?;
                }
                let ExprNode::ForallE {
                    binder_type,
                    body,
                    binder_info,
                    ..
                } = remainder.node()
                else {
                    return Err(unsupported("a decreasing argument in every member"));
                };
                if *binder_info != BinderInfo::Default
                    || !self.defeq_guarded(binder_type, &domain)?
                {
                    return Err(unsupported("the same structural family in every member"));
                }
                components.push(self.substitute(body, &Expr::fvar(major.id.clone()))?);
            }
            let mut product = components.last().cloned().ok_or_else(scope)?;
            for component in components.iter().rev().skip(1) {
                product = self.structural_pair_type(component.clone(), product)?;
            }
            let sort = self.known_type(&product)?.ok_or_else(scope)?;
            let universe = self.sort_level(&Typed {
                value: product.clone(),
                type_: sort,
            })?;
            let motive = self.structural_close(&product, std::slice::from_ref(&major), true)?;
            let mut universes = if definition.base.level_params.len() == levels.len() {
                Vec::new()
            } else {
                vec![universe]
            };
            universes.extend(levels.iter().cloned());
            if universes.len() != definition.base.level_params.len() {
                return Err(unsupported(
                    "the family's course-of-values universe telescope",
                ));
            }
            let mut recursor = Typed {
                value: Expr::const_(brec, universes.clone()),
                type_: self.instantiate_params(
                    &definition.base.type_,
                    &definition.base.level_params,
                    &universes,
                )?,
            };
            for parameter in parameters {
                recursor = self.course_apply(recursor, parameter)?;
            }
            recursor = self.course_apply(recursor, motive)?;
            self.flush(true)?;
            let mut closed_components = Vec::new();
            for component in components {
                let component =
                    self.structural_close(&component, std::slice::from_ref(&major), true)?;
                closed_components.push(self.structural_close(&component, &fixed_locals, true)?);
            }
            let plan = StructuralPlan {
                name: Name::str(names[0].clone(), "_mutual"),
                names,
                types,
                level_params,
                arities,
                fixed,
                family: family_name.clone(),
                family_parameters: family.num_params as usize,
                domain: self.structural_close(&domain, &fixed_locals, true)?,
                recursor: self.structural_close(&recursor.value, &fixed_locals, true)?,
                recursor_type: self.structural_close(&recursor.type_, &fixed_locals, true)?,
                components: closed_components,
            };
            for term in [&plan.domain, &plan.recursor, &plan.recursor_type]
                .into_iter()
                .chain(&plan.components)
            {
                self.require_resolved_terms(std::slice::from_ref(term))?;
                if term.has_fvar() || term.has_loose_bvars() || term.has_level_mvar() {
                    return Err(scope());
                }
            }
            Ok(plan)
        })();
        self.txn.lctx = saved;
        result
    }

    fn structural_recursor_at(
        &mut self,
        plan: &StructuralPlan,
        fixed: &[Expr],
        major: Expr,
    ) -> Result<(Typed, Expr, Expr), NatDefinitionElabError> {
        let recursor = Typed {
            value: self.structural_open(&plan.recursor, fixed)?,
            type_: self.structural_open(&plan.recursor_type, fixed)?,
        };
        let recursor = self.course_apply(recursor, major.clone())?;
        let remaining = self.whnf(&recursor.type_)?;
        let ExprNode::ForallE {
            binder_type: functional,
            ..
        } = remaining.node()
        else {
            return Err(scope());
        };
        let function = self.whnf(functional)?;
        let ExprNode::ForallE { body, .. } = function.node() else {
            return Err(scope());
        };
        let at = self.substitute(body, &major)?;
        let at = self.whnf(&at)?;
        let ExprNode::ForallE {
            binder_type: below, ..
        } = at.node()
        else {
            return Err(scope());
        };
        Ok((recursor, functional.clone(), below.clone()))
    }

    /// Elaborate one source body against the shared below dictionary and retain its closed
    /// functional component. Return only that member's reducible projection wrapper.
    pub(in crate::source) fn mutual_structural_body(
        &mut self,
        name: &Name,
        parameters: &[LocalDecl],
        syntax: &Syntax,
        expected: Option<Expr>,
        hint: Option<&TerminationHint<'_>>,
        header_parameters: usize,
    ) -> Result<Typed, NatDefinitionElabError> {
        let member = self.mutual_structural_member.clone().ok_or_else(scope)?;
        let plan = member.plan;
        if plan.names.get(member.index) != Some(name) || member.active.is_some() {
            return Err(scope());
        }
        let mut parameters = parameters.to_vec();
        let (body, expected, lambdas) =
            self.open_recursive_lambdas(syntax, expected, &mut parameters)?;
        let expected = expected.ok_or_else(|| error(RecursionError::ResultTypeRequired))?;
        if parameters.len() != plan.arities[member.index] || parameters.len() <= plan.fixed {
            return Err(unsupported("the same body telescope as its planned header"));
        }
        match hint {
            Some(TerminationHint::Structural(hint)) => {
                if self.structural_hint_parameter(hint, &parameters, header_parameters)?
                    != plan.fixed
                {
                    return Err(unsupported(
                        "a structural hint selecting the first varying argument",
                    ));
                }
            }
            None | Some(TerminationHint::Automatic) => {}
            _ => return Err(unsupported("structural or automatic termination hints")),
        }
        let fixed = parameters[..plan.fixed].to_vec();
        let fixed_values: Vec<_> = fixed
            .iter()
            .map(|local| Expr::fvar(local.id.clone()))
            .collect();
        let major = &parameters[plan.fixed];
        let major_value = Expr::fvar(major.id.clone());
        let (_, _, below_type) =
            self.structural_recursor_at(&plan, &fixed_values, major_value.clone())?;
        let saved = self.txn.lctx.clone();
        let below_name = self.fresh_name()?;
        let below = self
            .txn
            .lctx
            .add_param(
                FVarId(below_name.clone()),
                below_name.clone(),
                below_type,
                BinderInfo::Default,
            )
            .clone();
        let mut references = Vec::new();
        let mut markers = Vec::new();
        for type_ in &plan.types {
            self.tick()?;
            let marker = FVarId(self.fresh_name()?);
            self.txn.lctx.add_param(
                marker.clone(),
                marker.0.clone(),
                type_.clone(),
                BinderInfo::Default,
            );
            references.push(Typed {
                value: Expr::fvar(marker.clone()),
                type_: type_.clone(),
            });
            markers.push(marker);
        }
        self.mutual_structural_member
            .as_mut()
            .ok_or_else(scope)?
            .active = Some(Active {
            fixed: fixed.clone(),
            below: below_name,
            references,
            markers: markers.clone(),
        });
        let result = (|| {
            let term = self.term(body, Some(expected.clone()))?;
            self.resolve_instances_with_defaults()?;
            self.resume_postponed_eliminators(true)?;
            self.flush(true)?;
            self.complete_local_functions()?;
            let mut value = self.instantiate(&term.value)?;
            let reads = self.elimination_reads(&value)?;
            if markers.iter().any(|marker| reads.contains(marker)) {
                return Err(error(RecursionError::PartialApplication));
            }
            value = self.structural_close(&value, &parameters[plan.fixed + 1..], true)?;
            value = self.structural_close(&value, std::slice::from_ref(&below), true)?;
            value = self.structural_close(&value, std::slice::from_ref(major), true)?;
            value = self.structural_close(&value, &fixed, true)?;
            let mut piece = Typed {
                value,
                type_: expected.clone(),
            };
            // Peers outside this SCC retain the ordinary group's header references until
            // closed. They are not recursive targets of this below dictionary.
            self.close_partial_group_references(&mut piece)?;
            self.require_resolved_terms(std::slice::from_ref(&piece.value))?;
            if piece.value.has_fvar()
                || piece.value.has_loose_bvars()
                || piece.value.has_level_mvar()
            {
                return Err(scope());
            }
            Ok(piece.value)
        })();
        self.mutual_structural_member
            .as_mut()
            .ok_or_else(scope)?
            .active = None;
        self.txn.lctx = saved;
        self.mutual_structural_member
            .as_mut()
            .ok_or_else(scope)?
            .piece = Some(result?);
        let levels = plan
            .level_params
            .iter()
            .cloned()
            .map(Level::param)
            .collect();
        let mut wrapper = fixed_values
            .into_iter()
            .fold(Expr::const_(plan.name.clone(), levels), Expr::app);
        wrapper = Expr::app(wrapper, major_value);
        wrapper = project(wrapper, member.index, plan.names.len());
        for parameter in &parameters[plan.fixed + 1..] {
            wrapper = Expr::app(wrapper, Expr::fvar(parameter.id.clone()));
        }
        self.close_recursive_lambdas(
            &lambdas,
            Typed {
                value: wrapper,
                type_: expected,
            },
        )
    }

    /// Replace a complete recursive call only after the ordinary course-of-values selector
    /// finds that exact smaller argument. The number/type of product components cannot make
    /// a nondecreasing or unrelated argument eligible.
    pub(in crate::source) fn lower_mutual_structural_call(
        &mut self,
        value: &Expr,
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        let Some(member) = self.mutual_structural_member.clone() else {
            return Ok(None);
        };
        let Some(active) = member.active else {
            return Ok(None);
        };
        if !value.has_fvar() {
            return Ok(None);
        }
        let (head, arguments) = self.course_spine(value)?;
        let ExprNode::FVar { id } = head.node() else {
            return Ok(None);
        };
        let Some(target) = active.markers.iter().position(|marker| marker == id) else {
            return Ok(None);
        };
        let plan = member.plan;
        if arguments.len() <= plan.fixed {
            return Ok(None);
        }
        if arguments
            .iter()
            .any(|argument| argument.has_expr_mvar() || argument.has_level_mvar())
        {
            self.flush(false)?;
        }
        let arguments = arguments
            .iter()
            .map(|argument| self.instantiate(argument))
            .collect::<Result<Vec<_>, _>>()?;
        for (argument, parameter) in arguments.iter().zip(&active.fixed) {
            if !self.fixed_recursive_argument(argument, parameter)? {
                return Err(error(RecursionError::ChangedParameter));
            }
        }
        let requested = &arguments[plan.fixed];
        let reads = self.elimination_reads(requested)?;
        if active.markers.iter().any(|marker| reads.contains(marker)) {
            return Err(error(RecursionError::NotDecreasing));
        }
        let below = self
            .txn
            .lctx
            .find_by_user_name(&active.below)
            .cloned()
            .ok_or_else(|| error(RecursionError::NotDecreasing))?;
        let entry = self.select_course_entry(
            &below,
            &plan.family,
            plan.family_parameters,
            std::slice::from_ref(requested),
        )?;
        let mut result = project(entry, target, plan.names.len());
        for argument in arguments.into_iter().skip(plan.fixed + 1) {
            self.tick()?;
            result = Expr::app(result, argument);
        }
        Ok(Some(result))
    }

    pub(in crate::source) fn assemble_mutual_structural(
        &mut self,
        plan: &StructuralPlan,
        pieces: &[Expr],
        obligations: &[Typed],
    ) -> Result<DefinitionVal, NatDefinitionElabError> {
        if pieces.len() != plan.names.len() || obligations.len() != pieces.len() {
            return Err(scope());
        }
        self.level_params = plan.level_params.clone();
        self.explicit_levels = plan.level_params.len();
        let saved = self.txn.lctx.clone();
        let result = (|| {
            let (fixed, _) = self.structural_fixed_locals(&plan.types[0], plan.fixed)?;
            let fixed_values: Vec<_> = fixed
                .iter()
                .map(|local| Expr::fvar(local.id.clone()))
                .collect();
            let domain = self.structural_open(&plan.domain, &fixed_values)?;
            let major_id = FVarId(self.fresh_name()?);
            let major = self
                .txn
                .lctx
                .add_param(major_id, Name::anonymous(), domain, BinderInfo::Default)
                .clone();
            let major_value = Expr::fvar(major.id.clone());
            let (recursor, functional_type, below_type) =
                self.structural_recursor_at(&plan, &fixed_values, major_value.clone())?;
            let below_id = FVarId(self.fresh_name()?);
            let below = self
                .txn
                .lctx
                .add_param(below_id, Name::anonymous(), below_type, BinderInfo::Default)
                .clone();
            let mut entries = Vec::new();
            for (piece, component) in pieces.iter().zip(&plan.components) {
                let piece = self.structural_open(piece, &fixed_values)?;
                let value = self.structural_open(
                    &piece,
                    &[major_value.clone(), Expr::fvar(below.id.clone())],
                )?;
                let component = self.structural_open(component, &fixed_values)?;
                let type_ = self.structural_open(&component, std::slice::from_ref(&major_value))?;
                entries.push(Typed { value, type_ });
            }
            let mut product = entries.pop().ok_or_else(scope)?;
            for entry in entries.into_iter().rev() {
                product = self.structural_pair(entry, product)?;
            }
            let functional =
                self.structural_close(&product.value, &[major.clone(), below], true)?;
            let checked = self.match_apply(
                recursor,
                Typed {
                    value: functional,
                    type_: functional_type,
                },
            )?;
            let mut value =
                self.structural_close(&checked.value, std::slice::from_ref(&major), true)?;
            let mut type_ =
                self.structural_close(&checked.type_, std::slice::from_ref(&major), false)?;
            value = self.structural_close(&value, &fixed, true)?;
            type_ = self.structural_close(&type_, &fixed, false)?;
            // Original bodies, abstracted over all recursive references, are checked even
            // where normalization of the compiled function would erase an annotation.
            for obligation in obligations.iter().rev() {
                value = Expr::let_e(
                    Name::anonymous(),
                    obligation.type_.clone(),
                    obligation.value.clone(),
                    value,
                    false,
                );
            }
            self.flush(true)?;
            value = self.instantiate(&value)?;
            type_ = self.instantiate(&type_)?;
            self.require_resolved_terms(&[value.clone(), type_.clone()])?;
            if value.has_fvar()
                || type_.has_fvar()
                || value.has_loose_bvars()
                || type_.has_loose_bvars()
            {
                return Err(scope());
            }
            Ok(DefinitionVal {
                base: ConstantVal {
                    name: plan.name.clone(),
                    level_params: plan.level_params.clone(),
                    type_,
                },
                value,
                hints: ReducibilityHints::Regular(1),
                safety: DefinitionSafety::Safe,
                all: vec![plan.name.clone()],
            })
        })();
        self.txn.lctx = saved;
        result
    }
}
