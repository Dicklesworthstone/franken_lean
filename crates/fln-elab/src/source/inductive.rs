//! Source constructor telescopes are elaborated in isolated local contexts.
//! The provisional family is a local type parameter, never an unchecked global.
use super::*;
use crate::inductive::{ConstructorSpec, InductiveError, InductiveSpec, inductive_declaration};
use crate::records::{Builder, RecordBudget};

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
            level_params: vec![],
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
    expect_empty_null(&id[1], "absent explicit universe parameters")?;
    let Syntax::Ident { val: name, .. } = &id[0] else {
        return Err(invalid());
    };
    if name.is_anonymous() || env.contains(name) {
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
    let mut context = Context::new(env, kernel);
    let mut parameters = context.bind_parameters(&sig[0])?;
    if parameters.iter().any(|p| &p.user_name == name) {
        return Err(invalid());
    }
    let explicit = if let Some(annotation) = optional_type_syntax(&sig[1])? {
        let value = context.type_term(annotation)?;
        let value = checked_type(&mut context, value, budget)?;
        let value = context.whnf(&value)?;
        let ExprNode::Sort { level } = value.node() else {
            return Err(invalid());
        };
        Some(level.clone())
    } else {
        None
    };
    let provisional = explicit.clone().unwrap_or_else(Level::one);
    if !provisional.is_never_zero() || provisional.has_mvar() {
        return Err(failure(SourceInferenceError::Inductive(
            InductiveError::UnsupportedSort,
        )));
    }
    let mut closer = Builder {
        remaining: budget.max_nodes,
    };
    let family_type = closer
        .close(&parameters, Expr::sort(provisional), false, false)
        .map_err(|e| failure(SourceInferenceError::Inductive(e.into())))?;
    let self_id = FVarId(context.fresh_name()?);
    context.txn.lctx.add_param(
        self_id.clone(),
        name.clone(),
        family_type,
        BinderInfo::Default,
    );
    let base = context.txn.lctx.clone();
    let family = parameters.iter().fold(Expr::fvar(self_id.clone()), |f, p| {
        Expr::app(f, Expr::fvar(p.id.clone()))
    });
    let mut constructors = Vec::new();
    let mut annotations = Vec::new();
    let mut inferred = Level::one();
    let mut count = parameters.len();
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
            loop {
                context.tick()?;
                head = without_ascription(head);
                let ExprNode::App { f, .. } = head.node() else {
                    break;
                };
                head = f.clone();
            }
            if !matches!(head.node(), ExprNode::FVar { id } if id == &self_id) {
                return Err(invalid());
            }
            let family = context.instantiate(&family)?;
            context
                .txn
                .unify(&result, &family, UnificationBudget::new(kernel))
                .map_err(|e| failure(SourceInferenceError::Unification(Box::new(e))))?;
            // Later constructors can raise the family's universe. Keep the raw
            // annotation and its original telescope until that universe is final.
            annotations.push((annotation, annotation_context));
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
        for field in &mut fields {
            let domain = context.instantiate(&field.type_)?;
            let ty = context.known_type(&domain)?.ok_or_else(invalid)?;
            let completed = context.finish(Typed {
                value: domain,
                type_: ty,
            })?;
            let universe = context.sort_level(&completed)?;
            inferred = Level::max(inferred, universe).map_err(|_| invalid())?;
            // Replace only the provisional family identity. Parameter and field
            // locals stay available for the candidate builder to close exactly.
            field.type_ = completed
                .value
                .abstract_fvar(&self_id, 0)
                .map_err(|_| invalid())?
                .subst_loose(0, &[Expr::const_(name.clone(), vec![])])
                .map_err(|_| invalid())?;
        }
        constructors.push(ConstructorSpec {
            name: ctor_name.clone(),
            fields,
        });
    }
    for parameter in &mut parameters {
        parameter.type_ = context.instantiate(&parameter.type_)?;
        context.require_resolved(std::slice::from_ref(&parameter.type_))?;
    }
    context.resolve_instances(true)?;
    context.flush(true)?;
    let result_level = explicit.unwrap_or(inferred);
    let family_type = closer
        .close(&parameters, Expr::sort(result_level.clone()), false, false)
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
    let specification = InductiveSpec {
        name: name.clone(),
        level_params: vec![],
        parameters,
        constructors,
        result_level,
    };
    inductive_declaration(&specification, budget)
        .map_err(|e| failure(SourceInferenceError::Inductive(e)))
}
