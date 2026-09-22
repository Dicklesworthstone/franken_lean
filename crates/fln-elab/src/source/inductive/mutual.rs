//! Source mutual blocks share local family assumptions, never provisional globals.
//! All headers precede all bodies. The sole output is one candidate authority unit
//! for the ordinary kernel and independent-checker admission path.
use super::*;
use crate::inductive::mutual_inductive_declaration;
use std::collections::HashSet;

fn rename(
    context: &mut Context,
    mut term: Expr,
    replacements: &[(FVarId, Expr)],
) -> Result<Expr, NatDefinitionElabError> {
    for (id, value) in replacements {
        context.tick()?;
        term = term
            .abstract_fvar(id, 0)
            .map_err(|_| invalid())?
            .subst_loose(0, std::slice::from_ref(value))
            .map_err(|_| invalid())?;
    }
    Ok(term)
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

/// Elaborate two to eight uniform, positive data families as one indivisible
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
    let mut explicit = None::<Level>;
    let mut declared_levels = Vec::new();
    for h in &headers {
        if !names.insert(h.name.clone()) {
            return Err(invalid());
        }
        if let Some(level) = &h.explicit {
            if !level.is_never_zero()
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
        for name in &h.context.level_params[..h.context.explicit_levels] {
            if !declared_levels.contains(name) {
                declared_levels.push(name.clone());
            }
        }
    }
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
        if family != 0 && h.parameters.len() != common.len() {
            return Err(invalid());
        }
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
        for index in &mut h.indices {
            let ty = h.context.instantiate(&index.type_)?;
            h.context.require_resolved(std::slice::from_ref(&ty))?;
            index.type_ = rename(&mut h.context, ty, &replacements)?;
        }
        // Canonicalize written parameters without discarding the lexical
        // section context used by their domains and by later constructor fields.
        h.context.txn.lctx = scope.variables.locals().clone();
        for (i, p) in h.parameters.iter_mut().enumerate() {
            if family == 0 {
                common.push(p.clone());
            } else {
                if p.binder_info != common[i].binder_info {
                    return Err(invalid());
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
    for (i, h) in headers.iter_mut().enumerate() {
        for ((id, name), ty) in ids.iter().zip(&family_names).zip(&initial_types) {
            h.context.tick()?;
            h.context
                .txn
                .lctx
                .add_param(id.clone(), name.clone(), ty.clone(), BinderInfo::Default);
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
    let result_level = explicit.unwrap_or(inferred);
    let final_types = headers
        .iter()
        .map(|h| family_type(h, &result_level, budget))
        .collect::<Result<Vec<_>, _>>()?;
    let mut roots = final_types.clone();
    for body in &all_bodies {
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
    for (mut h, mut body) in headers.into_iter().zip(all_bodies) {
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
    mutual_inductive_declaration(&specs, budget)
        .map_err(|e| failure(SourceInferenceError::Inductive(e)))
}
