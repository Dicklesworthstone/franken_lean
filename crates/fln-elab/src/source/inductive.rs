//! Source constructor telescopes are elaborated in isolated local contexts.
//! The provisional family is a local type parameter, never an unchecked global.
use super::*;
use crate::inductive::{
    ConstructorSpec, InductiveError, InductiveSpec, inductive_with_field_universes,
};
use crate::records::{Builder, RecordBudget};

mod mutual;
pub(super) use mutual::elaborate_mutual;

pub fn is_inductive(syntax: &Syntax) -> bool {
    matches!(syntax,Syntax::Node { kind,args,.. } if kind == &parser_kind(&["Command","declaration"])
        && matches!(args.as_slice(),[_,Syntax::Node { kind,.. }] if kind == &parser_kind(&["Command","inductive"])))
}
fn invalid() -> NatDefinitionElabError {
    failure(SourceInferenceError::Inductive(
        InductiveError::InvalidTelescope,
    ))
}

/// Reduction may discard source ascriptions and unused arguments. Check the
/// unreduced type in its complete telescope first; this candidate is never
/// published, and a non-answer retains its kernel outcome.
fn checked_type(
    context: &mut Context,
    value: Expr,
    budget: RecordBudget,
) -> Result<Expr, NatDefinitionElabError> {
    let type_ = context.known_type(&value)?.ok_or_else(invalid)?;
    let term = context.finish(Typed { value, type_ })?;
    let mut locals = context.txn.lctx.decls().to_vec();
    for local in &mut locals {
        local.type_ = context.instantiate(&local.type_)?;
        context.require_resolved(std::slice::from_ref(&local.type_))?;
    }
    let mut closer = Builder {
        remaining: budget.max_nodes,
    };
    let type_ = closer
        .close(&locals, term.value.clone(), false, false)
        .map_err(|e| failure(SourceInferenceError::Inductive(e.into())))?;
    let name = loop {
        let name = context.fresh_name()?;
        if !context.txn.env.contains(&name) {
            break name;
        }
    };
    let candidate = Declaration::Axiom(fln_env::constants::AxiomVal {
        base: ConstantVal {
            name,
            level_params: context.level_params.clone(),
            type_,
        },
        is_unsafe: false,
    });
    match check(&context.txn.env, &candidate, context.kernel) {
        Outcome::Complete(Verdict::Accepted { .. }) => Ok(term.value),
        outcome => Err(failure(SourceInferenceError::TypeObligation(Box::new(
            outcome,
        )))),
    }
}

/// Source ascriptions are retained as identity lets until checked_type checks
/// them. Remove only that encoding when inspecting the constructor's head.
fn without_ascription(mut value: Expr) -> Expr {
    loop {
        match value.node() {
            ExprNode::MData { expr, .. } => value = expr.clone(),
            ExprNode::LetE {
                decl_name,
                value: inner,
                body,
                ..
            } if decl_name.is_anonymous() && matches!(body.node(), ExprNode::BVar { idx: 0 }) => {
                value = inner.clone();
            }
            _ => return value,
        }
    }
}

pub fn elaborate_inductive(
    syntax: &Syntax,
    env: &Environment,
    kernel: Budget,
    budget: RecordBudget,
) -> Result<Declaration, NatDefinitionElabError> {
    elaborate_inductive_scoped(syntax, env, kernel, budget, &SourceScope::default())
}

struct Header<'a> {
    context: Context,
    name: Name,
    parameters: Vec<LocalDecl>,
    indices: Vec<LocalDecl>,
    explicit: Option<Level>,
    family_type: Expr,
    ctors: &'a [Syntax],
}

fn header<'a>(
    syntax: &'a Syntax,
    env: &Environment,
    kernel: Budget,
    budget: RecordBudget,
    scope: &SourceScope,
) -> Result<Header<'a>, NatDefinitionElabError> {
    let root = expect_node(
        syntax,
        &parser_kind(&["Command", "declaration"]),
        2,
        "inductive declaration",
    )?;
    let modifiers = expect_node(
        &root[0],
        &parser_kind(&["Command", "declModifiers"]),
        7,
        "inductive modifiers",
    )?;
    for part in modifiers {
        expect_empty_null(part, "absent inductive modifiers")?;
    }
    let parts = expect_node(
        &root[1],
        &parser_kind(&["Command", "inductive"]),
        7,
        "inductive command",
    )?;
    expect_atom(&parts[0], "inductive", "inductive keyword")?;
    let id = expect_node(
        &parts[1],
        &parser_kind(&["Command", "declId"]),
        2,
        "inductive name",
    )?;
    // Explicit parameters are installed before opening the family telescope.
    let Syntax::Ident { val: name, .. } = &id[0] else {
        return Err(invalid());
    };
    if name.is_anonymous() {
        return Err(invalid());
    }
    let sig = expect_node(
        &parts[2],
        &parser_kind(&["Command", "optDeclSig"]),
        2,
        "inductive signature",
    )?;
    match expect_null_args(&parts[3], "inductive body keyword")? {
        [] => {}
        [Syntax::Atom { val, .. }] if val == "where" || val == ":=" => {}
        _ => return Err(invalid()),
    }
    expect_empty_null(&parts[5], "unsupported computed inductive fields")?;
    let deriving = expect_node(
        &parts[6],
        &parser_kind(&["Command", "optDeriving"]),
        1,
        "inductive deriving",
    )?;
    expect_empty_null(&deriving[0], "unsupported deriving")?;
    let ctors = expect_null_args(&parts[4], "constructors")?;
    if ctors.len() > budget.max_binders {
        return Err(failure(SourceInferenceError::ResourceLimit));
    }
    let mut context = Context::scoped(env, kernel, scope);
    let name = context.enter_declaration(name)?;
    if env.contains(&name) {
        return Err(invalid());
    }
    context.declare_levels(&id[1])?;
    context.infer_level_params = true;
    let parameters = context.bind_parameters(&sig[0])?;
    if parameters.iter().any(|p| p.user_name == name) {
        return Err(invalid());
    }
    let parameter_context = context.txn.lctx.clone();
    let mut indices = Vec::new();
    let explicit = if let Some(annotation) = optional_type_syntax(&sig[1])? {
        let value = context.type_term(annotation)?;
        let value = checked_type(&mut context, value, budget)?;
        let mut value = context.whnf(&value)?;
        while let ExprNode::ForallE {
            binder_name,
            binder_type,
            body,
            binder_info,
        } = value.node()
        {
            context.tick()?;
            if parameters.len().saturating_add(indices.len()) >= budget.max_binders {
                return Err(failure(SourceInferenceError::ResourceLimit));
            }
            let id = FVarId(context.fresh_name()?);
            context.txn.lctx.add_param(
                id.clone(),
                binder_name.clone(),
                binder_type.clone(),
                *binder_info,
            );
            indices.push(
                context
                    .txn
                    .lctx
                    .find(&id)
                    .expect("new family index")
                    .clone(),
            );
            let body = context.substitute(body, &Expr::fvar(id))?;
            value = context.whnf(&body)?;
        }
        let ExprNode::Sort { level } = value.node() else {
            return Err(invalid());
        };
        Some(level.clone())
    } else {
        None
    };
    context.txn.lctx = parameter_context;
    let provisional = explicit.clone().unwrap_or_else(Level::one);
    if (!provisional.is_never_zero() && !provisional.normalize_fixpoint().is_zero())
        || provisional.has_mvar()
    {
        return Err(failure(SourceInferenceError::Inductive(
            InductiveError::UnsupportedSort,
        )));
    }
    let mut closer = Builder {
        remaining: budget.max_nodes,
    };
    let indexed_result = closer
        .close(&indices, Expr::sort(provisional), false, false)
        .map_err(|e| failure(SourceInferenceError::Inductive(e.into())))?;
    let family_type = closer
        .close(&parameters, indexed_result, false, false)
        .map_err(|e| failure(SourceInferenceError::Inductive(e.into())))?;
    Ok(Header {
        context,
        name,
        parameters,
        indices,
        explicit,
        family_type,
        ctors,
    })
}

pub(super) fn elaborate_inductive_scoped(
    syntax: &Syntax,
    env: &Environment,
    kernel: Budget,
    budget: RecordBudget,
    scope: &SourceScope,
) -> Result<Declaration, NatDefinitionElabError> {
    let Header {
        mut context,
        name,
        mut parameters,
        mut indices,
        explicit,
        family_type,
        ctors,
    } = header(syntax, env, kernel, budget, scope)?;
    let self_id = FVarId(context.fresh_name()?);
    context.txn.lctx.add_param(
        self_id.clone(),
        name.clone(),
        family_type,
        BinderInfo::Default,
    );
    let Bodies {
        mut constructors,
        field_universes,
        annotations,
        inferred,
    } = bodies(&mut context, &parameters, &indices, &self_id, ctors, budget)?;
    for parameter in &mut parameters {
        parameter.type_ = context.instantiate(&parameter.type_)?;
        context.require_resolved(std::slice::from_ref(&parameter.type_))?;
    }
    for index in &mut indices {
        index.type_ = context.instantiate(&index.type_)?;
        context.require_resolved(std::slice::from_ref(&index.type_))?;
    }
    context.resolve_instances(true)?;
    context.flush(true)?;
    let result_level = explicit.unwrap_or(inferred);
    let mut closer = Builder {
        remaining: budget.max_nodes,
    };
    let indexed_result = closer
        .close(&indices, Expr::sort(result_level.clone()), false, false)
        .map_err(|e| failure(SourceInferenceError::Inductive(e.into())))?;
    let family_type = closer
        .close(&parameters, indexed_result, false, false)
        .map_err(|e| failure(SourceInferenceError::Inductive(e.into())))?;
    for (annotation, locals) in annotations {
        let mut final_context = LocalContext::new();
        for local in locals.decls() {
            let type_ = if local.id == self_id {
                family_type.clone()
            } else {
                local.type_.clone()
            };
            if let Some(value) = &local.value {
                final_context.add_let(
                    local.id.clone(),
                    local.user_name.clone(),
                    type_,
                    value.clone(),
                );
            } else {
                final_context.add_param(
                    local.id.clone(),
                    local.user_name.clone(),
                    type_,
                    local.binder_info,
                );
            }
        }
        context.txn.lctx = final_context;
        checked_type(&mut context, annotation, budget)?;
    }
    let mut roots = vec![family_type];
    for ctor in &constructors {
        roots.extend(ctor.fields.iter().map(|f| f.type_.clone()));
        roots.extend(ctor.result_indices.iter().cloned());
    }
    // Local recursive references keep the written-parameter interface until
    // every constructor is elaborated. Only then can field-only dependencies
    // determine the shared section prefix for the family and its constructors.
    let section = section_prefix(&mut context, &mut roots)?;
    let level_params = context.declaration_levels(&roots)?;
    let mut family_constant = Expr::const_(
        name.clone(),
        level_params.iter().cloned().map(Level::param).collect(),
    );
    for parameter in &section {
        context.tick()?;
        family_constant = Expr::app(family_constant, Expr::fvar(parameter.id.clone()));
    }
    parameters.splice(0..0, section);
    for ctor in &mut constructors {
        for field in &mut ctor.fields {
            field.type_ = field
                .type_
                .abstract_fvar(&self_id, 0)
                .map_err(|_| invalid())?
                .subst_loose(0, std::slice::from_ref(&family_constant))
                .map_err(|_| invalid())?;
        }
        for index in &mut ctor.result_indices {
            *index = index
                .abstract_fvar(&self_id, 0)
                .map_err(|_| invalid())?
                .subst_loose(0, std::slice::from_ref(&family_constant))
                .map_err(|_| invalid())?;
        }
    }
    let specification = InductiveSpec {
        name,
        level_params,
        parameters,
        indices,
        constructors,
        result_level,
    };
    inductive_with_field_universes(&specification, budget, &field_universes)
        .map_err(|e| failure(SourceInferenceError::Inductive(e)))
}

/// Select actual type/constructor dependencies, not theorem-only include/omit
/// choices. Domains contribute universe dependencies even when a selected local
/// appears only as a free-variable leaf in the constructor types.
fn section_prefix(
    context: &mut Context,
    roots: &mut Vec<Expr>,
) -> Result<Vec<LocalDecl>, NatDefinitionElabError> {
    let mut section = context.section_parameters(roots, false)?;
    for parameter in &mut section {
        context.tick()?;
        parameter.type_ = context.instantiate(&parameter.type_)?;
        context.require_resolved(std::slice::from_ref(&parameter.type_))?;
        roots.push(parameter.type_.clone());
    }
    Ok(section)
}

struct Bodies {
    constructors: Vec<ConstructorSpec>,
    field_universes: Vec<Vec<Level>>,
    annotations: Vec<(Expr, LocalContext)>,
    inferred: Level,
}

fn bodies(
    context: &mut Context,
    parameters: &[LocalDecl],
    indices: &[LocalDecl],
    self_id: &FVarId,
    ctors: &[Syntax],
    budget: RecordBudget,
) -> Result<Bodies, NatDefinitionElabError> {
    let kernel = context.kernel;
    let base = context.txn.lctx.clone();
    let family = parameters.iter().fold(Expr::fvar(self_id.clone()), |f, p| {
        Expr::app(f, Expr::fvar(p.id.clone()))
    });
    let mut constructors = Vec::new();
    let mut field_universes = Vec::new();
    let mut annotations = Vec::new();
    let mut inferred = Level::one();
    let mut count = parameters.len().saturating_add(indices.len());
    for ctor in ctors {
        context.tick()?;
        context.txn.lctx = base.clone();
        let parts = expect_node(
            ctor,
            &parser_kind(&["Command", "ctor"]),
            5,
            "inductive constructor",
        )?;
        expect_empty_null(&parts[0], "absent constructor documentation")?;
        expect_atom(&parts[1], "|", "constructor separator")?;
        let modifiers = expect_node(
            &parts[2],
            &parser_kind(&["Command", "declModifiers"]),
            7,
            "constructor modifiers",
        )?;
        for part in modifiers {
            expect_empty_null(part, "absent constructor modifier")?;
        }
        let Syntax::Ident { val: ctor_name, .. } = &parts[3] else {
            return Err(invalid());
        };
        let sig = expect_node(
            &parts[4],
            &parser_kind(&["Command", "optDeclSig"]),
            2,
            "constructor signature",
        )?;
        let mut fields = context.bind_parameters(&sig[0])?;
        let mut result_indices = Vec::new();
        if let Some(result) = optional_type_syntax(&sig[1])? {
            let annotation = context.type_term(result)?;
            let annotation_context = context.txn.lctx.clone();
            let mut result = annotation.clone();
            loop {
                context.tick()?;
                let reduced = without_ascription(context.instantiate(&result)?);
                let ExprNode::ForallE {
                    binder_name,
                    binder_type,
                    body,
                    binder_info,
                } = reduced.node()
                else {
                    break;
                };
                if count.saturating_add(fields.len()) >= budget.max_binders {
                    return Err(failure(SourceInferenceError::ResourceLimit));
                }
                let id = FVarId(context.fresh_name()?);
                context.txn.lctx.add_param(
                    id.clone(),
                    binder_name.clone(),
                    binder_type.clone(),
                    *binder_info,
                );
                fields.push(
                    context
                        .txn
                        .lctx
                        .find(&id)
                        .expect("new constructor field")
                        .clone(),
                );
                result = context.substitute(body, &Expr::fvar(id))?;
            }
            // Constructor result annotations are obligations, never hints to
            // discard. This is the same local family and uniform parameters.
            let result = without_ascription(context.instantiate(&result)?);
            let mut head = result.clone();
            let mut arguments = Vec::new();
            loop {
                context.tick()?;
                head = without_ascription(head);
                let ExprNode::App { f, a } = head.node() else {
                    break;
                };
                arguments.push(a.clone());
                head = f.clone();
            }
            if !matches!(head.node(), ExprNode::FVar { id } if id == self_id) {
                return Err(invalid());
            }
            arguments.reverse();
            if arguments.len() != parameters.len() + indices.len() {
                return Err(invalid());
            }
            result_indices = arguments[parameters.len()..].to_vec();
            let result_prefix = arguments[..parameters.len()]
                .iter()
                .cloned()
                .fold(head, Expr::app);
            let family = context.instantiate(&family)?;
            context
                .txn
                .unify(&result_prefix, &family, UnificationBudget::new(kernel))
                .map_err(|e| failure(SourceInferenceError::Unification(Box::new(e))))?;
            // Later constructors can raise the family's universe. Keep the raw
            // annotation and its original telescope until that universe is final.
            annotations.push((annotation, annotation_context));
        } else if !indices.is_empty() {
            // There is no determined result index to infer from an omitted
            // result signature. Never invent an index or silently add a field.
            return Err(invalid());
        }
        context.resolve_instances(true)?;
        context.flush(true)?;
        count = count
            .checked_add(fields.len())
            .and_then(|n| n.checked_add(1))
            .ok_or_else(|| failure(SourceInferenceError::ResourceLimit))?;
        if count > budget.max_binders {
            return Err(failure(SourceInferenceError::ResourceLimit));
        }
        let mut universes = Vec::with_capacity(fields.len());
        for field in &mut fields {
            let domain = context.instantiate(&field.type_)?;
            let ty = context.known_type(&domain)?.ok_or_else(invalid)?;
            let completed = context.finish(Typed {
                value: domain,
                type_: ty,
            })?;
            let universe = context.sort_level(&completed)?;
            universes.push(universe.clone());
            inferred = Level::max(inferred, universe).map_err(|_| invalid())?;
            // Replace only the provisional family identity. Parameter and field
            // locals stay available for the candidate builder to close exactly.
            field.type_ = completed.value;
        }
        for index in &mut result_indices {
            *index = context.instantiate(index)?;
            context.require_resolved(std::slice::from_ref(index))?;
        }
        field_universes.push(universes);
        constructors.push(ConstructorSpec {
            name: ctor_name.clone(),
            fields,
            result_indices,
        });
    }
    Ok(Bodies {
        constructors,
        field_universes,
        annotations,
        inferred,
    })
}
