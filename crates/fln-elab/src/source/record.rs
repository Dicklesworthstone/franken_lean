//! Source record signatures elaborate through the same bidirectional context as
//! ordinary definitions. Result universes follow field domains unless explicit.
use super::*;
use crate::records::defaults::{RecordDefault, helper_name};
use crate::records::{RecordBudget, RecordSpec, record_declarations};

#[derive(Debug)]
pub struct SourceRecord {
    pub name: Name,
    pub is_class: bool,
    /// The inductive block followed by each projection, all still untrusted.
    pub declarations: Vec<Declaration>,
    /// References only: the caller registers these after admitting the full batch.
    pub defaults: Vec<RecordDefault>,
}

pub fn is_record(syntax: &Syntax) -> bool {
    matches!(syntax, Syntax::Node { kind, args, .. }
        if kind == &parser_kind(&["Command", "declaration"])
        && matches!(args.as_slice(), [_, Syntax::Node { kind, .. }]
            if kind == &parser_kind(&["Command", "structure"])))
}

fn empty_modifiers(syntax: &Syntax) -> Result<(), NatDefinitionElabError> {
    let parts = expect_node(
        syntax,
        &parser_kind(&["Command", "declModifiers"]),
        7,
        "record modifiers",
    )?;
    for part in parts {
        expect_empty_null(part, "absent record modifiers")?;
    }
    Ok(())
}

/// Elaborate a Type-valued, nonrecursive structure/class with named fields.
/// Registration is intentionally absent here: only checked successors can own it.
pub fn elaborate_record(
    syntax: &Syntax,
    environment: &Environment,
    kernel: Budget,
    budget: RecordBudget,
) -> Result<SourceRecord, NatDefinitionElabError> {
    let root = expect_node(
        syntax,
        &parser_kind(&["Command", "declaration"]),
        2,
        "record declaration",
    )?;
    empty_modifiers(&root[0])?;
    let parts = expect_node(
        &root[1],
        &parser_kind(&["Command", "structure"]),
        6,
        "structure command",
    )?;
    let is_class = matches!(&parts[0], Syntax::Node { kind, .. } if kind == &parser_kind(&["Command", "classTk"]));
    let keyword = expect_node(
        &parts[0],
        &parser_kind(&["Command", if is_class { "classTk" } else { "structureTk" }]),
        1,
        "record keyword",
    )?;
    expect_atom(
        &keyword[0],
        if is_class { "class" } else { "structure" },
        "record keyword",
    )?;
    let id = expect_node(
        &parts[1],
        &parser_kind(&["Command", "declId"]),
        2,
        "record name",
    )?;
    expect_empty_null(&id[1], "absent universe declarations")?;
    let Syntax::Ident { val: name, .. } = &id[0] else {
        return Err(NatDefinitionElabError::AnonymousDeclarationName);
    };
    if name.is_anonymous() {
        return Err(NatDefinitionElabError::AnonymousDeclarationName);
    }
    expect_empty_null(&parts[3], "unsupported inheritance")?;
    let deriving = expect_node(
        &parts[5],
        &parser_kind(&["Command", "optDeriving"]),
        1,
        "deriving suffix",
    )?;
    expect_empty_null(&deriving[0], "unsupported deriving")?;
    let signature = expect_node(
        &parts[2],
        &parser_kind(&["Command", "optDeclSig"]),
        2,
        "record signature",
    )?;
    let mut context = Context::new(environment, kernel);
    let parameters = context.bind_parameters(&signature[0])?;
    let explicit = optional_type_syntax(&signature[1])?
        .map(|s| context.term(s, None))
        .transpose()?;
    let mut inferred = Level::one();
    let fields = match expect_null_args(&parts[4], "record body")? {
        [] => &[][..],
        [keyword, ctor, fields] => {
            expect_atom(keyword, "where", "record body keyword")?;
            expect_empty_null(ctor, "unsupported custom constructor")?;
            let fields = expect_node(
                fields,
                &parser_kind(&["Command", "structFields"]),
                1,
                "record fields",
            )?;
            expect_null_args(&fields[0], "record field array")?
        }
        _ => return Err(failure(SourceInferenceError::Scope)),
    };
    if parameters.len().saturating_add(fields.len()) > budget.max_binders {
        return Err(failure(SourceInferenceError::Record(
            crate::records::RecordError::ResourceLimit,
        )));
    }
    let mut output = Vec::new();
    let mut defaults = Vec::new();
    let mut helpers = Vec::new();
    for field in fields {
        context.tick()?;
        let parts = expect_node(
            field,
            &parser_kind(&["Command", "structSimpleBinder"]),
            4,
            "named structure field",
        )?;
        empty_modifiers(&parts[0])?;
        let default = match expect_null_args(&parts[3], "field default")? {
            [] => None,
            [syntax] => {
                let parts = expect_node(
                    syntax,
                    &parser_kind(&["Term", "binderDefault"]),
                    2,
                    "field default value",
                )?;
                expect_atom(&parts[0], ":=", "field default assignment")?;
                Some(&parts[1])
            }
            _ => return Err(failure(SourceInferenceError::Scope)),
        };
        let Syntax::Ident { val: user_name, .. } = &parts[1] else {
            return Err(failure(SourceInferenceError::Scope));
        };
        let sig = expect_node(
            &parts[2],
            &parser_kind(&["Command", "optDeclSig"]),
            2,
            "field signature",
        )?;
        let saved = context.txn.lctx.clone();
        let arguments = context.bind_parameters(&sig[0])?;
        let annotation = optional_type_syntax(&sig[1])?
            .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
        let mut domain = context.type_term(annotation)?;
        if let Some(syntax) = default {
            let term = context.term(syntax, Some(domain.clone()))?;
            // Preserve the declared type even when the default is never selected.
            // Its ordinary helper declaration must still pass kernel checking.
            let mut term = context.finish(Typed {
                value: term.value,
                type_: domain.clone(),
            })?;
            let locals = context.txn.lctx.decls().to_vec();
            for (index, local) in locals.iter().enumerate().rev() {
                context.tick()?;
                let local_type = context.instantiate(&local.type_)?;
                let style = if index < parameters.len() && local.binder_info == BinderInfo::Default
                {
                    BinderInfo::Implicit
                } else {
                    local.binder_info
                };
                term.value = term
                    .value
                    .abstract_fvar(&local.id, 0)
                    .map_err(|_| failure(SourceInferenceError::Scope))?;
                term.type_ = term
                    .type_
                    .abstract_fvar(&local.id, 0)
                    .map_err(|_| failure(SourceInferenceError::Scope))?;
                term.value = Expr::lam(
                    local.user_name.clone(),
                    local_type.clone(),
                    term.value,
                    style,
                );
                term.type_ = Expr::forall_e(local.user_name.clone(), local_type, term.type_, style);
            }
            let helper = helper_name(name, user_name);
            helpers.push(Declaration::Defn(DefinitionVal {
                base: ConstantVal {
                    name: helper.clone(),
                    level_params: Vec::new(),
                    type_: term.type_,
                },
                value: term.value,
                hints: ReducibilityHints::Abbrev,
                safety: DefinitionSafety::Safe,
                all: vec![helper.clone()],
            }));
            defaults.push(RecordDefault {
                record: name.clone(),
                field: u32::try_from(output.len())
                    .map_err(|_| failure(SourceInferenceError::ResourceLimit))?,
                helper,
            });
        }
        for arg in arguments.iter().rev() {
            context.tick()?;
            domain = domain
                .abstract_fvar(&arg.id, 0)
                .map_err(|_| failure(SourceInferenceError::Scope))?;
            domain = Expr::forall_e(
                arg.user_name.clone(),
                arg.type_.clone(),
                domain,
                arg.binder_info,
            );
        }
        context.txn.lctx = saved;
        let type_ = context
            .known_type(&domain)?
            .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
        let completed = context.finish(Typed {
            value: domain,
            type_,
        })?;
        let universe = context.sort_level(&completed)?;
        inferred =
            Level::max(inferred, universe).map_err(|_| failure(SourceInferenceError::Scope))?;
        let id = FVarId(context.fresh_name()?);
        context.txn.lctx.add_param(
            id.clone(),
            user_name.clone(),
            completed.value,
            BinderInfo::Default,
        );
        output.push(
            context
                .txn
                .lctx
                .find(&id)
                .expect("inserted record field")
                .clone(),
        );
    }
    let result_level = match explicit {
        Some(term) => {
            let term = context.finish(term)?;
            let sort = context.whnf(&term.value)?;
            let ExprNode::Sort { level } = sort.node() else {
                return Err(failure(SourceInferenceError::ExpectedType));
            };
            level.clone()
        }
        None => inferred,
    };
    let mut parameters = parameters;
    for param in &mut parameters {
        param.type_ = context.instantiate(&param.type_)?;
    }
    let spec = RecordSpec {
        name: name.clone(),
        level_params: Vec::new(),
        parameters,
        fields: output,
        result_level,
        is_class,
    };
    let mut declarations =
        record_declarations(&spec, budget).map_err(|e| failure(SourceInferenceError::Record(e)))?;
    declarations.extend(helpers);
    Ok(SourceRecord {
        name: name.clone(),
        is_class,
        declarations,
        defaults,
    })
}
