//! Source mutual blocks share local family assumptions, never provisional globals.
//! All headers precede all bodies. The sole output is one candidate authority unit
//! for the ordinary kernel and independent-checker admission path.
use super::*;
use crate::inductive::mutual_inductive_with_promoted_parameters;
use fln_core::name::LeafView;
use std::collections::HashSet;

fn header_error(error: MutualHeaderError) -> NatDefinitionElabError {
    failure(SourceInferenceError::MutualHeader(error))
}

/// A member's universe names as the pin's mismatch message lists them: the declared
/// `.{…}` names, then the section's `universe` names, each reversed (`expandDeclId`
/// conses each onto `levelNames`). Measured at the pin: `universe w x` with
/// `Forest.{v}` prints `` `v`, `x`, `w` ``.
fn printed_levels(header: &Header<'_>, scope: &SourceScope) -> Vec<Name> {
    let declared = &header.context.level_params[..header.context.explicit_levels];
    declared
        .iter()
        .rev()
        .chain(scope.universes.iter().rev())
        .cloned()
        .collect()
}

/// A binder name this elaborator generated (`Context::fresh_name`) for an anonymous
/// binder. It stands for the macro-scoped name the pin generates there.
fn generated(name: &Name) -> bool {
    matches!(name.leaf_view(), LeafView::Num(_))
        && name.parent() == Name::from_components(["_fln_source"])
}

fn family_type(
    header: &Header<'_>,
    level: &Level,
    budget: RecordBudget,
) -> Result<Expr, NatDefinitionElabError> {
    let mut closer = Builder {
        remaining: budget.max_nodes,
    };
    let result = closer
        .close(&header.indices, Expr::sort(level.clone()), false, false)
        .map_err(|e| failure(SourceInferenceError::Inductive(e.into())))?;
    closer
        .close(&header.parameters, result, false, false)
        .map_err(|e| failure(SourceInferenceError::Inductive(e.into())))
}

/// Elaborate two to eight uniform, positive families as one indivisible
/// candidate. This is source elaboration, not admission. Unsupported nested
/// families, negative occurrences and nonuniform parameters are refused by the
/// shared native inductive generator; no member is installed speculatively.
pub(in crate::source) fn elaborate_mutual(
    syntax: &[Syntax],
    env: &Environment,
    kernel: Budget,
    budget: RecordBudget,
    scope: &SourceScope,
) -> Result<Declaration, NatDefinitionElabError> {
    if !(2..=8).contains(&syntax.len()) {
        return Err(invalid());
    }
    let mut headers = syntax
        .iter()
        .map(|s| header(s, env, kernel, budget, scope))
        .collect::<Result<Vec<_>, _>>()?;
    let mut names = HashSet::new();
    for h in &headers {
        if !names.insert(h.name.clone()) {
            return Err(invalid());
        }
    }
    // The pin's header checks, in its order: universe names, then the parameter count
    // over every member, then each later member's parameters against the first's (below,
    // binder annotation, name, type), and the result sort last.
    let first_levels = printed_levels(&headers[0], scope);
    for h in &headers[1..] {
        let levels = printed_levels(h, scope);
        if levels != first_levels {
            return Err(header_error(MutualHeaderError::UniverseParameters {
                declaration: h.short_name.clone(),
                names: levels,
                first: headers[0].short_name.clone(),
                first_names: first_levels,
            }));
        }
    }
    for h in &headers[1..] {
        if h.parameters.len() != headers[0].parameters.len() {
            return Err(header_error(MutualHeaderError::ParameterCount {
                declaration: h.short_name.clone(),
                count: h.parameters.len(),
                first: headers[0].short_name.clone(),
                first_count: headers[0].parameters.len(),
            }));
        }
    }
    // Every member declares the same names (checked above).
    let declared_levels =
        headers[0].context.level_params[..headers[0].context.explicit_levels].to_vec();
    let mut levels = declared_levels.clone();
    for h in &headers {
        for level in &h.context.level_params {
            if !levels.contains(level) {
                levels.push(level.clone());
            }
        }
    }
    let mut common = Vec::<LocalDecl>::new();
    for (family, h) in headers.iter_mut().enumerate() {
        let replacements: Vec<_> = h
            .parameters
            .iter()
            .enumerate()
            .map(|(i, p)| {
                let id = FVarId(Name::num(
                    Name::from_components(["_fln_mutual_param"]),
                    i as u64,
                ));
                (p.id.clone(), Expr::fvar(id))
            })
            .collect();
        // Validate every original parameter before conversion can discard an
        // ascription. A sibling must not borrow the first family's validity.
        for p in &h.parameters {
            checked_type(&mut h.context, p.type_.clone(), budget)?;
        }
        for (i, p) in h.parameters.iter_mut().enumerate() {
            let ty = h.context.instantiate(&p.type_)?;
            h.context.require_resolved(std::slice::from_ref(&ty))?;
            p.type_ = rename(&mut h.context, ty, &replacements)?;
            let ExprNode::FVar { id } = replacements[i].1.node() else {
                unreachable!()
            };
            p.id = id.clone();
        }
        // Indices get block-unique identities too: promotion renames a
        // sibling's constructor fields onto the first family's indices, and
        // locals from different members' contexts may share a name.
        let mut index_replacements = Vec::new();
        for (j, index) in h.indices.iter_mut().enumerate() {
            let ty = h.context.instantiate(&index.type_)?;
            h.context.require_resolved(std::slice::from_ref(&ty))?;
            let ty = rename(&mut h.context, ty, &replacements)?;
            index.type_ = rename(&mut h.context, ty, &index_replacements)?;
            let id = FVarId(Name::num(
                Name::num(Name::from_components(["_fln_mutual_index"]), family as u64),
                j as u64,
            ));
            index_replacements.push((index.id.clone(), Expr::fvar(id.clone())));
            index.id = id;
        }
        // Canonicalize written parameters without discarding the lexical
        // section context used by their domains and by later constructor fields.
        h.context.txn.lctx = scope.variables.locals().clone();
        for (i, p) in h.parameters.iter_mut().enumerate() {
            if family == 0 {
                common.push(p.clone());
            } else {
                if p.binder_info != common[i].binder_info {
                    return Err(header_error(MutualHeaderError::BinderAnnotation {
                        parameter: p.user_name.clone(),
                    }));
                }
                let anonymous_instances = p.binder_info == BinderInfo::InstImplicit
                    && generated(&p.user_name)
                    && generated(&common[i].user_name);
                if p.user_name != common[i].user_name && !anonymous_instances {
                    return Err(header_error(MutualHeaderError::ParameterNames {
                        found: p.user_name.clone(),
                        expected: common[i].user_name.clone(),
                    }));
                }
                h.context
                    .txn
                    .unify(&p.type_, &common[i].type_, UnificationBudget::new(kernel))
                    .map_err(|e| failure(SourceInferenceError::Unification(Box::new(e))))?;
                p.type_ = common[i].type_.clone();
            }
            h.context.txn.lctx.add_param(
                p.id.clone(),
                p.user_name.clone(),
                p.type_.clone(),
                p.binder_info,
            );
        }
        h.context.level_params = levels.clone();
        h.context.explicit_levels = declared_levels.len();
    }
    let mut explicit = None::<Level>;
    for h in &headers {
        if let Some(level) = &h.explicit {
            let normalized = level.normalize_fixpoint();
            // `checkResultingUniversePolymorphism` in the pin's source
            // elaborator permits Prop or a definitely nonzero universe by
            // default. Kernel-level generation also supports Sort u, but that
            // does not enable the separate bootstrap option in source files.
            if level.has_mvar()
                || (!normalized.is_zero() && !normalized.is_never_zero())
                || explicit
                    .as_ref()
                    .is_some_and(|other| other.normalize_fixpoint() != level.normalize_fixpoint())
            {
                return Err(failure(SourceInferenceError::Inductive(
                    InductiveError::UnsupportedSort,
                )));
            }
            explicit = Some(level.clone());
        }
    }
    let provisional = explicit.clone().unwrap_or_else(Level::one);
    let ids: Vec<_> = (0..headers.len())
        .map(|i| {
            FVarId(Name::num(
                Name::from_components(["_fln_mutual_family"]),
                i as u64,
            ))
        })
        .collect();
    let initial_types = headers
        .iter()
        .map(|h| family_type(h, &provisional, budget))
        .collect::<Result<Vec<_>, _>>()?;
    let family_names: Vec<_> = headers.iter().map(|h| h.name.clone()).collect();
    let mut all_bodies = Vec::new();
    let mut inferred = Level::one();
    let mut base = LocalContext::new();
    for (i, h) in headers.iter_mut().enumerate() {
        for ((id, name), ty) in ids.iter().zip(&family_names).zip(&initial_types) {
            h.context.tick()?;
            h.context
                .txn
                .lctx
                .add_param(id.clone(), name.clone(), ty.clone(), BinderInfo::Default);
        }
        if i == 0 {
            base = h.context.txn.lctx.clone();
        }
        let result = bodies(
            &mut h.context,
            &h.parameters,
            &h.indices,
            &ids[i],
            h.ctors,
            budget,
        )?;
        inferred = Level::max(inferred, result.inferred.clone()).map_err(|_| invalid())?;
        for name in &h.context.level_params {
            if !levels.contains(name) {
                levels.push(name.clone());
            }
        }
        all_bodies.push(result);
    }
    // The pin promotes a prefix of indices fixed across the whole block to
    // parameters (`fixedIndicesToParams` over every member): measured at the pin,
    // `Tree`/`Forest : Nat → Type` whose constructors all take and return `(n : Nat)`
    // print `number of parameters: 1`. The family types are unchanged; every
    // member's promoted parameters are the first member's indices.
    let count = {
        let families: Vec<_> = headers
            .iter()
            .zip(&all_bodies)
            .zip(&ids)
            .map(|((h, body), id)| (h.indices.clone(), id.clone(), body.constructors.clone()))
            .collect();
        let families: Vec<_> = families
            .iter()
            .map(|(indices, id, constructors)| PromotionFamily {
                indices,
                id,
                constructors,
            })
            .collect();
        let parameters = headers[0].parameters.clone();
        promotable_indices(&mut headers[0].context, &base, &parameters, &families)?
    };
    let mut promoted: Vec<Vec<Vec<LocalDecl>>> = all_bodies
        .iter()
        .map(|body| vec![Vec::new(); body.constructors.len()])
        .collect();
    if count > 0 {
        let lead: Vec<LocalDecl> = headers[0].indices[..count].to_vec();
        for ((h, body), own_binders) in headers.iter_mut().zip(&mut all_bodies).zip(&mut promoted) {
            let own: Vec<LocalDecl> = h.indices.drain(..count).collect();
            let to_lead: Vec<_> = own
                .iter()
                .zip(&lead)
                .map(|(own, lead)| (own.id.clone(), Expr::fvar(lead.id.clone())))
                .collect();
            for index in &mut h.indices {
                index.type_ = rename(&mut h.context, index.type_.clone(), &to_lead)?;
            }
            *own_binders =
                promote_constructors(&mut h.context, &lead, &mut body.constructors, None)?;
            // A member keeps its own binder name in its own type; the identity,
            // domain and binder style are the first member's, as the block shares them.
            h.parameters
                .extend(own.into_iter().zip(&lead).map(|(mut own, lead)| {
                    own.id = lead.id.clone();
                    own.type_ = lead.type_.clone();
                    own.binder_info = lead.binder_info;
                    own
                }));
        }
    }
    let result_level = explicit.unwrap_or(inferred);
    let final_types = headers
        .iter()
        .map(|h| family_type(h, &result_level, budget))
        .collect::<Result<Vec<_>, _>>()?;
    let mut roots = final_types.clone();
    for (body, own_binders) in all_bodies.iter().zip(&promoted) {
        roots.extend(own_binders.iter().flatten().map(|b| b.type_.clone()));
        for ctor in &body.constructors {
            roots.extend(ctor.fields.iter().map(|f| f.type_.clone()));
            roots.extend(ctor.result_indices.iter().cloned());
        }
    }
    for (h, body) in headers.iter_mut().zip(&mut all_bodies) {
        h.context.level_params = levels.clone();
        for (annotation, locals) in std::mem::take(&mut body.annotations) {
            let mut final_context = LocalContext::new();
            for local in locals.decls() {
                h.context.tick()?;
                let ty = ids
                    .iter()
                    .position(|id| id == &local.id)
                    .map_or_else(|| local.type_.clone(), |i| final_types[i].clone());
                if let Some(value) = &local.value {
                    final_context.add_let(
                        local.id.clone(),
                        local.user_name.clone(),
                        ty,
                        value.clone(),
                    );
                } else {
                    final_context.add_param(
                        local.id.clone(),
                        local.user_name.clone(),
                        ty,
                        local.binder_info,
                    );
                }
            }
            h.context.txn.lctx = final_context;
            checked_type(&mut h.context, annotation, budget)?;
        }
    }
    // All members share one uniform section telescope, including dependencies
    // used only by a sibling. Provisional local family types intentionally had
    // only written parameters; supply the captured prefix at every replacement.
    let context = &mut headers[0].context;
    let section = section_prefix(context, &mut roots)?;
    let level_params = context.declaration_levels(&roots)?;
    let mut replacements = Vec::new();
    for (id, name) in ids.into_iter().zip(&family_names) {
        context.tick()?;
        let mut value = Expr::const_(
            name.clone(),
            level_params.iter().cloned().map(Level::param).collect(),
        );
        for parameter in &section {
            context.tick()?;
            value = Expr::app(value, Expr::fvar(parameter.id.clone()));
        }
        replacements.push((id, value));
    }
    let mut specs = Vec::new();
    for ((mut h, mut body), own_binders) in headers.into_iter().zip(all_bodies).zip(&mut promoted) {
        for binder in own_binders.iter_mut().flatten() {
            binder.type_ = rename(&mut h.context, binder.type_.clone(), &replacements)?;
        }
        for ctor in &mut body.constructors {
            for field in &mut ctor.fields {
                field.type_ = rename(&mut h.context, field.type_.clone(), &replacements)?;
            }
            for index in &mut ctor.result_indices {
                *index = rename(&mut h.context, index.clone(), &replacements)?;
            }
        }
        h.parameters.splice(0..0, section.iter().cloned());
        specs.push(InductiveSpec {
            name: h.name,
            level_params: level_params.clone(),
            parameters: h.parameters,
            indices: h.indices,
            constructors: body.constructors,
            result_level: result_level.clone(),
        });
    }
    mutual_inductive_with_promoted_parameters(&specs, budget, &promoted)
        .map_err(|e| failure(SourceInferenceError::Inductive(e)))
}
