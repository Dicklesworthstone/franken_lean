//! A recursive component shares the inductive block's `brecOn` combinators. Each
//! family's motive packs the results of the source functions recursing on that family.
//! This is the same construction as the pin's Structural/BRecOn: recursive calls
//! select a component of the below dictionary,
//! never an unchecked definition or a well-founded substitute.
//!
//! Source bodies are elaborated with that dependent dictionary in scope. Ordinary match
//! elaboration then generalizes it over each constructor, including deeper subterms. The
//! existing canary-motive search identifies an entry by its smaller argument, not by its
//! result type. Every produced declaration still passes the ordinary two-checker batch.
use super::*;
use fln_env::constants::{ConstantInfo, DefinitionSafety, InductiveVal};
use std::sync::Arc;

pub(in crate::source) struct StructuralPlan {
    pub name: Name,
    pub names: Vec<Name>,
    pub types: Vec<Expr>,
    pub level_params: Vec<Name>,
    pub arities: Vec<usize>,
    pub fixed: usize,
    decreasing: usize,
    /// In the inductive block's motive order, including families with no source member.
    families: Vec<StructuralFamily>,
}

struct StructuralFamily {
    /// Source member indices packed into this family's motive, in component order.
    members: Vec<usize>,
    /// Empty families use the pin's neutral PUnit motive and functional.
    neutral: Option<Typed>,
    /// Source positions of the family's indices, in the family's telescope order.
    /// They occupy the varying prefix before the major, but need not occur in that order.
    indices: Vec<usize>,
    /// Other arguments between the fixed prefix and major, in source order. Each
    /// product component quantifies its own telescope at these positions so recursive
    /// calls may supply new values and different members may use different argument types.
    generalized: Vec<usize>,
    family: Name,
    family_parameters: usize,
    /// The domain is closed over the fixed prefix and then family-ordered indices.
    /// The recursor is closed over only the fixed prefix; its motive abstracts the indices.
    domain: Expr,
    recursor: Expr,
    recursor_type: Expr,
    /// Each component is closed over the fixed prefix, family-ordered indices and major.
    /// Its value quantifies generalized prefix arguments, then trailing arguments,
    /// followed by the member result.
    components: Vec<Expr>,
}

impl StructuralPlan {
    fn member_family(&self, member: usize) -> Option<(usize, &StructuralFamily, usize)> {
        self.families.iter().enumerate().find_map(|(index, family)| {
            family
                .members
                .iter()
                .position(|candidate| *candidate == member)
                .map(|position| (index, family, position))
        })
    }
}

#[derive(Clone)]
pub(in crate::source) struct StructuralMember {
    plan: Arc<StructuralPlan>,
    index: usize,
    captures: Vec<LocalDecl>,
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
    pub(in crate::source) fn new(
        plan: Arc<StructuralPlan>,
        index: usize,
        captures: Vec<LocalDecl>,
    ) -> Self {
        Self {
            plan,
            index,
            captures,
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

    /// Construct a shared motive over one inductive family. Independent local indices may
    /// occur between the common fixed prefix and the major; the motive abstracts them in
    /// family order. Other arguments in that prefix are quantified inside each component,
    /// whose generalized arguments, result type and trailing argument telescope may
    /// differ between members.
    pub(in crate::source) fn mutual_structural_plan(
        &mut self,
        names: Vec<Name>,
        types: Vec<Expr>,
        arities: Vec<usize>,
        fixed: usize,
        decreasing: usize,
        level_params: Vec<Name>,
    ) -> Result<StructuralPlan, NatDefinitionElabError> {
        if names.is_empty()
            || types.len() != names.len()
            || arities.len() != names.len()
            || decreasing < fixed
            || arities.iter().any(|arity| *arity <= decreasing)
        {
            return Err(unsupported("a decreasing argument in every member"));
        }
        self.level_params = level_params.clone();
        self.explicit_levels = level_params.len();
        let saved = self.txn.lctx.clone();
        let result = (|| {
            let (prefix_locals, first) = self.structural_fixed_locals(&types[0], decreasing)?;
            let fixed_locals = &prefix_locals[..fixed];
            let ExprNode::ForallE {
                binder_type: domain,
                ..
            } = first.node()
            else {
                return Err(unsupported("a structural argument"));
            };
            // The pin's Structural.getRecArgInfo considers every telescope local,
            // regardless of binder style. Only the shared motive's major is explicit;
            // the member types and wrappers retain their original binder information.
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
            if family.all.len() > 1 {
                return self.mutual_inductive_structural_plan(
                    StructuralPlan {
                        name: Name::str(names[0].clone(), "_mutual"),
                        names,
                        types,
                        level_params,
                        arities,
                        fixed,
                        decreasing,
                        families: Vec::new(),
                    },
                    &prefix_locals,
                    &family,
                    &parameters,
                    levels,
                );
            }
            if family.all.len() != 1
                || parameters.len() != family.num_params as usize + family.num_indices as usize
            {
                return Err(unsupported("one fully applied inductive family"));
            }
            let (parameters, index_values) = parameters.split_at(family.num_params as usize);
            let indices = match self.elimination_index_locals(index_values) {
                Err(NatDefinitionElabError::Inference(SourceInferenceError::Match(
                    matching::MatchError::UnrefinedIndices,
                ))) => return Err(unsupported("distinct local structural indices")),
                result => result?,
            };
            let mut index_positions = Vec::new();
            for index in &indices {
                let Some(position) = prefix_locals.iter().position(|local| local.id == index.id)
                else {
                    return Err(unsupported("structural indices preceding the major"));
                };
                if position < fixed {
                    return Err(unsupported("varying structural indices"));
                }
                index_positions.push(position);
            }
            let generalized_positions: Vec<_> = (fixed..decreasing)
                .filter(|position| !index_positions.contains(position))
                .collect();
            // Family parameters and index domains live outside the component's
            // generalized arguments. Check this reordered telescope before closing
            // it, so a dependency cannot escape its binder into the shared motive.
            let mut preceding: HashSet<_> =
                fixed_locals.iter().map(|local| local.id.clone()).collect();
            for parameter in parameters {
                if !self.elimination_reads(parameter)?.is_subset(&preceding) {
                    return Err(unsupported("family parameters in the common fixed prefix"));
                }
            }
            for index in &indices {
                if !self.elimination_reads(&index.type_)?.is_subset(&preceding) {
                    return Err(unsupported("structural index domains in family order"));
                }
                preceding.insert(index.id.clone());
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
                let mut generalized = Vec::new();
                for (position, local) in prefix_locals.iter().enumerate() {
                    self.tick()?;
                    let ExprNode::ForallE {
                        binder_name,
                        binder_type,
                        body,
                        binder_info,
                    } = remainder.node()
                    else {
                        return Err(unsupported("one common structural prefix"));
                    };
                    let argument = if generalized_positions.contains(&position) {
                        // Only the fixed parameters and family indices belong to the
                        // shared recursor telescope. Open each component's other
                        // binders independently: their domains may differ, and a later
                        // domain must refer to this member's preceding arguments.
                        let id = FVarId(self.fresh_name()?);
                        generalized.push(
                            self.txn
                                .lctx
                                .add_param(
                                    id.clone(),
                                    binder_name.clone(),
                                    binder_type.clone(),
                                    *binder_info,
                                )
                                .clone(),
                        );
                        Expr::fvar(id)
                    } else {
                        if !self.defeq_guarded(binder_type, &local.type_)? {
                            return Err(unsupported(
                                "shared structural prefix parameters of the same type",
                            ));
                        }
                        Expr::fvar(local.id.clone())
                    };
                    remainder = self.substitute(body, &argument)?;
                }
                let ExprNode::ForallE {
                    binder_type, body, ..
                } = remainder.node()
                else {
                    return Err(unsupported("a decreasing argument in every member"));
                };
                if !self.defeq_guarded(binder_type, &domain)? {
                    return Err(unsupported("the same structural family in every member"));
                }
                let component = self.substitute(body, &Expr::fvar(major.id.clone()))?;
                components.push(self.structural_close(&component, &generalized, false)?);
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
            let motive = self.structural_close(&motive, &indices, true)?;
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
                recursor = self.course_apply(recursor, parameter.clone())?;
            }
            recursor = self.course_apply(recursor, motive)?;
            self.flush(true)?;
            let mut closed_components = Vec::new();
            for component in components {
                let component =
                    self.structural_close(&component, std::slice::from_ref(&major), true)?;
                let component = self.structural_close(&component, &indices, true)?;
                closed_components.push(self.structural_close(&component, fixed_locals, true)?);
            }
            let domain = self.structural_close(&domain, &indices, true)?;
            let family = StructuralFamily {
                members: (0..names.len()).collect(),
                neutral: None,
                indices: index_positions,
                generalized: generalized_positions,
                family: family_name.clone(),
                family_parameters: family.num_params as usize,
                domain: self.structural_close(&domain, fixed_locals, true)?,
                recursor: self.structural_close(&recursor.value, fixed_locals, true)?,
                recursor_type: self.structural_close(&recursor.type_, fixed_locals, true)?,
                components: closed_components,
            };
            self.validate_structural_family(&family)?;
            Ok(StructuralPlan {
                name: Name::str(names[0].clone(), "_mutual"),
                names,
                types,
                level_params,
                arities,
                fixed,
                decreasing,
                families: vec![family],
            })
        })();
        self.txn.lctx = saved;
        result
    }

    fn validate_structural_family(
        &mut self,
        family: &StructuralFamily,
    ) -> Result<(), NatDefinitionElabError> {
        for term in [&family.domain, &family.recursor, &family.recursor_type]
            .into_iter()
            .chain(&family.components)
            .chain(
                family
                    .neutral
                    .iter()
                    .flat_map(|neutral| [&neutral.value, &neutral.type_]),
            )
        {
            self.require_resolved_terms(std::slice::from_ref(term))?;
            if term.has_fvar() || term.has_loose_bvars() || term.has_level_mvar() {
                return Err(scope());
            }
        }
        Ok(())
    }

    /// The pin packs source functions by inductive family, not into one motive for the
    /// whole component. Each sibling's brecOn receives the same complete motive vector.
    /// This construction covers nonindexed, nonnested mutual blocks; the existing
    /// single-family path retains its independently varying index support.
    fn mutual_inductive_structural_plan(
        &mut self,
        mut plan: StructuralPlan,
        prefix: &[LocalDecl],
        first: &InductiveVal,
        parameters: &[Expr],
        levels: &[Level],
    ) -> Result<StructuralPlan, NatDefinitionElabError> {
        if first.num_indices != 0
            || first.num_nested != 0
            || parameters.len() != first.num_params as usize
        {
            return Err(unsupported("nonindexed, nonnested mutual inductive families"));
        }
        let fixed = &prefix[..plan.fixed];
        let fixed_ids: HashSet<_> = fixed.iter().map(|local| local.id.clone()).collect();
        for parameter in parameters {
            if !self.elimination_reads(parameter)?.is_subset(&fixed_ids) {
                return Err(unsupported("family parameters in the common fixed prefix"));
            }
        }
        let mut majors = Vec::new();
        let mut domains = Vec::new();
        for name in &first.all {
            self.tick()?;
            let Some(ConstantInfo::Induct(family)) = self.txn.env.find(name) else {
                return Err(scope());
            };
            if family.all != first.all
                || family.num_params != first.num_params
                || family.num_indices != 0
                || family.num_nested != 0
                || family.is_unsafe
            {
                return Err(unsupported("one safe nonindexed mutual inductive block"));
            }
            let domain = parameters
                .iter()
                .cloned()
                .fold(Expr::const_(name.clone(), levels.to_vec()), Expr::app);
            let id = FVarId(self.fresh_name()?);
            majors.push(
                self.txn
                    .lctx
                    .add_param(id, Name::anonymous(), domain.clone(), BinderInfo::Default)
                    .clone(),
            );
            domains.push(domain);
        }
        let mut members = vec![Vec::new(); first.all.len()];
        let mut components = vec![Vec::new(); first.all.len()];
        for (member, type_) in plan.types.iter().enumerate() {
            let mut remainder = type_.clone();
            let mut generalized = Vec::new();
            for (position, common) in prefix.iter().enumerate() {
                self.tick()?;
                let ExprNode::ForallE {
                    binder_name,
                    binder_type,
                    body,
                    binder_info,
                } = remainder.node()
                else {
                    return Err(unsupported("one common structural prefix"));
                };
                let argument = if position < plan.fixed {
                    if !self.defeq_guarded(binder_type, &common.type_)? {
                        return Err(unsupported(
                            "shared structural prefix parameters of the same type",
                        ));
                    }
                    Expr::fvar(common.id.clone())
                } else {
                    let id = FVarId(self.fresh_name()?);
                    generalized.push(
                        self.txn
                            .lctx
                            .add_param(
                                id.clone(),
                                binder_name.clone(),
                                binder_type.clone(),
                                *binder_info,
                            )
                            .clone(),
                    );
                    Expr::fvar(id)
                };
                remainder = self.substitute(body, &argument)?;
            }
            let ExprNode::ForallE {
                binder_type, body, ..
            } = remainder.node()
            else {
                return Err(unsupported("a decreasing argument in every member"));
            };
            let domain = self.whnf(binder_type)?;
            let (head, _) = self.course_spine(&domain)?;
            let ExprNode::Const { name, .. } = head.node() else {
                return Err(unsupported("a member of the shared mutual inductive block"));
            };
            let Some(family) = first.all.iter().position(|candidate| candidate == name) else {
                return Err(unsupported("a member of the shared mutual inductive block"));
            };
            if !self.defeq_guarded(binder_type, &domains[family])? {
                return Err(unsupported("the same inductive parameters in every member"));
            }
            let component = self.substitute(body, &Expr::fvar(majors[family].id.clone()))?;
            components[family].push(self.structural_close(&component, &generalized, false)?);
            members[family].push(member);
        }
        let mut products = Vec::new();
        let mut common_universe: Option<Level> = None;
        for family_components in &components {
            let Some(mut product) = family_components.last().cloned() else {
                products.push(None);
                continue;
            };
            for component in family_components.iter().rev().skip(1) {
                product = self.structural_pair_type(component.clone(), product)?;
            }
            let type_ = self.known_type(&product)?.ok_or_else(scope)?;
            let universe = self.sort_level(&Typed {
                value: product.clone(),
                type_,
            })?;
            if let Some(expected) = &common_universe {
                if !self.defeq_guarded(
                    &Expr::sort(expected.clone()),
                    &Expr::sort(universe.clone()),
                )? {
                    return Err(unsupported("mutual structural results in one universe"));
                }
            } else {
                common_universe = Some(universe);
            }
            products.push(Some(product));
        }
        let universe = common_universe.ok_or_else(scope)?;
        let neutral = Typed {
            value: Expr::const_(
                Name::from_components(["PUnit", "unit"]),
                vec![universe.clone()],
            ),
            type_: Expr::const_(Name::from_components(["PUnit"]), vec![universe.clone()]),
        };
        let mut motives = Vec::new();
        for (product, major) in products.iter().zip(&majors) {
            motives.push(self.structural_close(
                product.as_ref().unwrap_or(&neutral.type_),
                std::slice::from_ref(major),
                true,
            )?);
        }
        for (index, name) in first.all.iter().enumerate() {
            let brec = Name::str(name.clone(), "brecOn");
            if !self.is_auxiliary_recursor(&brec)? {
                return Err(unsupported("admitted course-of-values recursors for every family"));
            }
            let Some(ConstantInfo::Defn(definition)) = self.txn.env.find(&brec).cloned() else {
                return Err(unsupported("admitted course-of-values recursors for every family"));
            };
            if definition.safety != DefinitionSafety::Safe {
                return Err(unsupported("safe course-of-values recursors for every family"));
            }
            let mut universes = vec![universe.clone()];
            universes.extend_from_slice(levels);
            if universes.len() != definition.base.level_params.len() {
                return Err(unsupported("the mutual course-of-values universe telescope"));
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
                recursor = self.course_apply(recursor, parameter.clone())?;
            }
            for motive in &motives {
                recursor = self.course_apply(recursor, motive.clone())?;
            }
            self.flush(true)?;
            let mut closed_components = Vec::new();
            for component in &components[index] {
                let component =
                    self.structural_close(component, std::slice::from_ref(&majors[index]), true)?;
                closed_components.push(self.structural_close(&component, fixed, true)?);
            }
            let family = StructuralFamily {
                members: members[index].clone(),
                neutral: if members[index].is_empty() {
                    Some(Typed {
                        value: self.instantiate(&neutral.value)?,
                        type_: self.instantiate(&neutral.type_)?,
                    })
                } else {
                    None
                },
                indices: Vec::new(),
                generalized: (plan.fixed..plan.decreasing).collect(),
                family: name.clone(),
                family_parameters: first.num_params as usize,
                domain: self.structural_close(&domains[index], fixed, true)?,
                recursor: self.structural_close(&recursor.value, fixed, true)?,
                recursor_type: self.structural_close(&recursor.type_, fixed, true)?,
                components: closed_components,
            };
            self.validate_structural_family(&family)?;
            plan.families.push(family);
        }
        Ok(plan)
    }

    fn structural_recursor_at(
        &mut self,
        plan: &StructuralPlan,
        family_index: usize,
        fixed: &[Expr],
        indices: &[Expr],
        major: Expr,
    ) -> Result<(Typed, Vec<Expr>, Expr), NatDefinitionElabError> {
        let family = plan.families.get(family_index).ok_or_else(scope)?;
        let mut recursor = Typed {
            value: self.structural_open(&family.recursor, fixed)?,
            type_: self.structural_open(&family.recursor_type, fixed)?,
        };
        for index in indices {
            recursor = self.course_apply(recursor, index.clone())?;
        }
        let recursor = self.course_apply(recursor, major.clone())?;
        // Every sibling recursor has one functional per family in motive order.
        // Open their telescope with real locals, then verify no functional's type
        // depends on an earlier functional before allowing those temporary locals out.
        let saved = self.txn.lctx.clone();
        let result = (|| {
            let mut remaining = recursor.type_.clone();
            let mut functionals = Vec::new();
            let mut markers = Vec::new();
            for _ in &plan.families {
                self.tick()?;
                remaining = self.whnf(&remaining)?;
                let ExprNode::ForallE {
                    binder_name,
                    binder_type,
                    body,
                    binder_info,
                } = remaining.node()
                else {
                    return Err(scope());
                };
                functionals.push(binder_type.clone());
                let marker = FVarId(self.fresh_name()?);
                self.txn.lctx.add_param(
                    marker.clone(),
                    binder_name.clone(),
                    binder_type.clone(),
                    *binder_info,
                );
                markers.push(marker.clone());
                remaining = self.substitute(body, &Expr::fvar(marker))?;
            }
            for functional in &functionals {
                let reads = self.elimination_reads(functional)?;
                if markers.iter().any(|marker| reads.contains(marker)) {
                    return Err(scope());
                }
            }
            Ok(functionals)
        })();
        self.txn.lctx = saved;
        let functionals: Vec<Expr> = result?;
        let mut function = functionals.get(family_index).ok_or_else(scope)?.clone();
        for index in indices {
            function = self.whnf(&function)?;
            let ExprNode::ForallE { body, .. } = function.node() else {
                return Err(scope());
            };
            function = self.substitute(body, index)?;
        }
        let function = self.whnf(&function)?;
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
        Ok((recursor, functionals, below.clone()))
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
        let (family_index, family, component_index) =
            plan.member_family(member.index).ok_or_else(scope)?;
        let mut parameters = parameters.to_vec();
        let (body, expected, lambdas) =
            self.open_recursive_lambdas(syntax, expected, &mut parameters)?;
        // Captures are implicit in source peer references, but explicit fixed
        // arguments of the shared recursor. Keep their original identities;
        // a written parameter can shadow the same section variable's name.
        let captures = member.captures;
        let header_parameters = header_parameters
            .checked_add(captures.len())
            .ok_or_else(scope)?;
        parameters.splice(0..0, captures.iter().cloned());
        let expected = expected.ok_or_else(|| error(RecursionError::ResultTypeRequired))?;
        if parameters.len() != plan.arities[member.index] || parameters.len() <= plan.decreasing {
            return Err(unsupported("the same body telescope as its planned header"));
        }
        match hint {
            Some(TerminationHint::Structural(hint)) => {
                if self.structural_hint_parameter(hint, &parameters, header_parameters)?
                    != plan.decreasing
                {
                    return Err(unsupported("a structural hint selecting the planned major"));
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
        let indices: Vec<_> = family
            .indices
            .iter()
            .map(|&position| parameters[position].clone())
            .collect();
        let index_values: Vec<_> = indices
            .iter()
            .map(|local| Expr::fvar(local.id.clone()))
            .collect();
        let generalized: Vec<_> = family
            .generalized
            .iter()
            .map(|&position| parameters[position].clone())
            .collect();
        let major = &parameters[plan.decreasing];
        let major_value = Expr::fvar(major.id.clone());
        let (_, _, below_type) = self.structural_recursor_at(
            &plan,
            family_index,
            &fixed_values,
            &index_values,
            major_value.clone(),
        )?;
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
            let mut reference = Typed {
                value: Expr::fvar(marker.clone()),
                type_: type_.clone(),
            };
            for capture in &captures {
                reference = self.course_apply(reference, Expr::fvar(capture.id.clone()))?;
            }
            references.push(reference);
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
            let mut piece = Typed {
                value: self.instantiate(&term.value)?,
                type_: expected.clone(),
            };
            // Peers outside this SCC receive the same common section closure.
            // Close their references before abstracting that capture prefix.
            self.close_partial_group_references(&mut piece)?;
            let mut value = piece.value;
            let reads = self.elimination_reads(&value)?;
            if markers.iter().any(|marker| reads.contains(marker)) {
                return Err(error(RecursionError::PartialApplication));
            }
            value = self.structural_close(&value, &parameters[plan.decreasing + 1..], true)?;
            value = self.structural_close(&value, &generalized, true)?;
            value = self.structural_close(&value, std::slice::from_ref(&below), true)?;
            value = self.structural_close(&value, std::slice::from_ref(major), true)?;
            value = self.structural_close(&value, &indices, true)?;
            value = self.structural_close(&value, &fixed, true)?;
            self.require_resolved_terms(std::slice::from_ref(&value))?;
            if value.has_fvar() || value.has_loose_bvars() || value.has_level_mvar() {
                return Err(scope());
            }
            Ok(value)
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
        wrapper = project(wrapper, family_index, plan.families.len());
        for index in index_values {
            wrapper = Expr::app(wrapper, index);
        }
        wrapper = Expr::app(wrapper, major_value);
        wrapper = project(wrapper, component_index, family.members.len());
        for parameter in &generalized {
            self.tick()?;
            wrapper = Expr::app(wrapper, Expr::fvar(parameter.id.clone()));
        }
        for parameter in &parameters[plan.decreasing + 1..] {
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
        let (_, family, component_index) = plan.member_family(target).ok_or_else(scope)?;
        if arguments.len() <= plan.decreasing {
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
        // A dictionary entry is identified by its complete indexed argument, never by
        // the result type or the major alone. Source and family index orders may differ.
        let mut requested: Vec<_> = family
            .indices
            .iter()
            .map(|&position| arguments[position].clone())
            .collect();
        requested.push(arguments[plan.decreasing].clone());
        for argument in &requested {
            let reads = self.elimination_reads(argument)?;
            if active.markers.iter().any(|marker| reads.contains(marker)) {
                return Err(error(RecursionError::NotDecreasing));
            }
        }
        let below = self
            .txn
            .lctx
            .find_by_user_name(&active.below)
            .cloned()
            .ok_or_else(|| error(RecursionError::NotDecreasing))?;
        let entry =
            self.select_course_entry(&below, &family.family, family.family_parameters, &requested)?;
        let mut result = project(entry, component_index, family.members.len());
        for &position in &family.generalized {
            self.tick()?;
            result = Expr::app(result, arguments[position].clone());
        }
        for argument in arguments.into_iter().skip(plan.decreasing + 1) {
            self.tick()?;
            result = Expr::app(result, argument);
        }
        Ok(Some(result))
    }

    /// Build one family's functional from exactly the source members assigned to it.
    /// Its telescope is supplied by the admitted brecOn, so a sibling's major or below
    /// dictionary cannot be substituted merely because the result types coincide.
    fn structural_functional(
        &mut self,
        family: &StructuralFamily,
        fixed: &[Expr],
        pieces: &[Expr],
        expected: &Expr,
    ) -> Result<Typed, NatDefinitionElabError> {
        if let Some(neutral) = &family.neutral {
            if !family.members.is_empty() || !family.components.is_empty() {
                return Err(scope());
            }
            return self.mutual_constant_function(expected.clone(), neutral);
        }
        if family.members.len() != family.components.len() {
            return Err(scope());
        }
        let saved = self.txn.lctx.clone();
        let result = (|| {
            let (locals, result_type) =
                self.structural_fixed_locals(expected, family.indices.len() + 2)?;
            let arguments: Vec<_> = locals
                .iter()
                .map(|local| Expr::fvar(local.id.clone()))
                .collect();
            let motive_arguments = &arguments[..arguments.len() - 1];
            let mut entries = Vec::new();
            for (&member, component) in family.members.iter().zip(&family.components) {
                let piece = pieces.get(member).ok_or_else(scope)?;
                let piece = self.structural_open(piece, fixed)?;
                let value = self.structural_open(&piece, &arguments)?;
                let component = self.structural_open(component, fixed)?;
                let type_ = self.structural_open(&component, motive_arguments)?;
                entries.push(Typed { value, type_ });
            }
            let mut product = entries.pop().ok_or_else(scope)?;
            for entry in entries.into_iter().rev() {
                product = self.structural_pair(entry, product)?;
            }
            if !self.defeq_guarded(&product.type_, &result_type)? {
                return Err(scope());
            }
            Ok(Typed {
                value: self.structural_close(&product.value, &locals, true)?,
                type_: expected.clone(),
            })
        })();
        self.txn.lctx = saved;
        result
    }

    /// Open the family-ordered indices, independently of any source member's
    /// generalized arguments. The returned domain mentions only these and the fixed prefix.
    fn structural_family_domain(
        &mut self,
        family: &StructuralFamily,
        fixed: &[Expr],
    ) -> Result<(Vec<LocalDecl>, Expr), NatDefinitionElabError> {
        let mut domain = self.structural_open(&family.domain, fixed)?;
        let mut indices = Vec::new();
        for _ in &family.indices {
            self.tick()?;
            let ExprNode::Lam {
                binder_name,
                binder_type,
                body,
                binder_info,
            } = domain.node()
            else {
                return Err(scope());
            };
            let id = FVarId(self.fresh_name()?);
            indices.push(
                self.txn
                    .lctx
                    .add_param(
                        id.clone(),
                        binder_name.clone(),
                        binder_type.clone(),
                        *binder_info,
                    )
                    .clone(),
            );
            domain = self.substitute(body, &Expr::fvar(id))?;
        }
        Ok((indices, domain))
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
            let mut functions = Vec::new();
            for (family_index, family) in plan.families.iter().enumerate() {
                let (indices, domain) = self.structural_family_domain(family, &fixed_values)?;
                let index_values: Vec<_> = indices
                    .iter()
                    .map(|local| Expr::fvar(local.id.clone()))
                    .collect();
                let major_id = FVarId(self.fresh_name()?);
                let major = self
                    .txn
                    .lctx
                    .add_param(major_id, Name::anonymous(), domain, BinderInfo::Default)
                    .clone();
                let (mut recursor, functionals, _) = self.structural_recursor_at(
                    plan,
                    family_index,
                    &fixed_values,
                    &index_values,
                    Expr::fvar(major.id.clone()),
                )?;
                for (owner, expected) in plan.families.iter().zip(&functionals) {
                    let functional =
                        self.structural_functional(owner, &fixed_values, pieces, expected)?;
                    recursor = self.match_apply(recursor, functional)?;
                }
                let value =
                    self.structural_close(&recursor.value, std::slice::from_ref(&major), true)?;
                let type_ =
                    self.structural_close(&recursor.type_, std::slice::from_ref(&major), false)?;
                functions.push(Typed {
                    value: self.structural_close(&value, &indices, true)?,
                    type_: self.structural_close(&type_, &indices, false)?,
                });
            }
            // Keep the historical one-family auxiliary unchanged in shape. Several
            // families share one product of their complete functions, whose wrappers
            // select the family before supplying its indices and major.
            let mut product = functions.pop().ok_or_else(scope)?;
            for function in functions.into_iter().rev() {
                product = self.structural_pair(function, product)?;
            }
            let mut value = self.structural_close(&product.value, &fixed, true)?;
            let mut type_ = self.structural_close(&product.type_, &fixed, false)?;
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
