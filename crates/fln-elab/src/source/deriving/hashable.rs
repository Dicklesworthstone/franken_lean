//! Checked Hashable derivation follows the pin's constructor-order fold.
//!
//! Every constructor field participates, including proofs and inherited
//! records. Direct recursive children use the checked recursor's induction
//! hypotheses; ordinary fields retain their selected Hashable dictionaries.
use super::*;

fn typed(context: &mut Context, value: Expr) -> Result<Typed, NatDefinitionElabError> {
    let type_ = context
        .known_type(&value)?
        .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
    Ok(Typed { value, type_ })
}

fn call(
    context: &mut Context,
    name: &str,
    arguments: &[Typed],
) -> Result<Typed, NatDefinitionElabError> {
    let mut function = context.constant(&named(name))?;
    for argument in arguments {
        function = context.match_apply(function, argument.clone())?;
    }
    Ok(function)
}

fn local(
    context: &mut Context,
    name: Name,
    type_: Expr,
    binder_info: BinderInfo,
) -> Result<LocalDecl, NatDefinitionElabError> {
    let id = FVarId(context.fresh_name()?);
    Ok(context
        .txn
        .lctx
        .add_param(id, name, type_, binder_info)
        .clone())
}

fn value(local: &LocalDecl) -> Typed {
    Typed {
        value: Expr::fvar(local.id.clone()),
        type_: local.type_.clone(),
    }
}

fn open_binder(
    context: &mut Context,
    cursor: &mut Expr,
) -> Result<LocalDecl, NatDefinitionElabError> {
    let normalized = context.whnf(cursor)?;
    let ExprNode::ForallE {
        binder_name,
        binder_type,
        body,
        binder_info,
    } = normalized.node()
    else {
        return Err(failure(SourceInferenceError::ExpectedFunction));
    };
    let local = local(
        context,
        binder_name.clone(),
        binder_type.clone(),
        *binder_info,
    )?;
    *cursor = context.substitute(body, &Expr::fvar(local.id.clone()))?;
    Ok(local)
}

/// Close only the constructor branch, leaving the helper header in scope.
fn bind(
    context: &mut Context,
    mut term: Typed,
    locals: &[LocalDecl],
) -> Result<Typed, NatDefinitionElabError> {
    for local in locals.iter().rev() {
        context.tick()?;
        let domain = context.instantiate(&local.type_)?;
        term.value = Expr::lam(
            local.user_name.clone(),
            domain.clone(),
            term.value
                .abstract_fvar(&local.id, 0)
                .map_err(|_| failure(SourceInferenceError::Scope))?,
            local.binder_info,
        );
        term.type_ = Expr::forall_e(
            local.user_name.clone(),
            domain,
            term.type_
                .abstract_fvar(&local.id, 0)
                .map_err(|_| failure(SourceInferenceError::Scope))?,
            local.binder_info,
        );
    }
    context.finish(term)
}

fn class_type(context: &mut Context, carrier: &Expr) -> Result<Typed, NatDefinitionElabError> {
    let carrier = typed(context, carrier.clone())?;
    let class = call(context, "Hashable", &[carrier])?;
    context.finish(class)
}

fn hash_field(context: &mut Context, field: &LocalDecl) -> Result<Typed, NatDefinitionElabError> {
    let class = class_type(context, &field.type_)?;
    let dictionary = context.instance_hole(class.value.clone())?;
    context.resolve_instances(true)?;
    let dictionary = Typed {
        value: context.instantiate(&dictionary)?,
        type_: class.value,
    };
    let carrier = typed(context, field.type_.clone())?;
    // In particular, proofs are not discarded here. The pin hashes them using
    // the ordinary instance (usually zero), then still performs the mix.
    call(
        context,
        "Hashable.hash",
        &[carrier, dictionary, value(field)],
    )
}

fn ordinal(context: &mut Context, index: usize) -> Result<Typed, NatDefinitionElabError> {
    let index = u64::try_from(index).map_err(|_| failure(SourceInferenceError::ResourceLimit))?;
    // The generated numeral is ordinary source notation: a scoped OfNat
    // instance must have the same effect here as in the pin's quotation.
    let syntax = Syntax::node(
        named("num"),
        vec![Syntax::atom(
            fln_syntax::source::SourceInfo::None,
            index.to_string(),
        )],
    );
    context
        .numeric_literal(&syntax, Some(&Expr::const_(named("UInt64"), Vec::new())))?
        .ok_or_else(|| failure(SourceInferenceError::InstanceSynthesisRequired(None)))
}

fn family_indices(
    context: &mut Context,
    family: &InductiveVal,
    target: &Expr,
) -> Result<(Vec<LocalDecl>, Expr), NatDefinitionElabError> {
    let mut target = typed(context, target.clone())?;
    let mut indices = Vec::new();
    for _ in 0..family.num_indices {
        context.tick()?;
        let cursor = context.whnf(&target.type_)?;
        let ExprNode::ForallE {
            binder_name,
            binder_type,
            ..
        } = cursor.node()
        else {
            return Err(unsupported(&family.base.name));
        };
        let index = local(
            context,
            binder_name.clone(),
            binder_type.clone(),
            BinderInfo::Implicit,
        )?;
        target = context.match_apply(target, value(&index))?;
        indices.push(index);
    }
    Ok((indices, target.value))
}

fn hash_body(
    context: &mut Context,
    family: &InductiveVal,
    parameters: &[LocalDecl],
    indices: &[LocalDecl],
    target: &Expr,
    receiver: &LocalDecl,
) -> Result<Typed, NatDefinitionElabError> {
    let recursor_name = Name::str(family.base.name.clone(), "rec");
    let Some(ConstantInfo::Rec(metadata)) = context.txn.env.find(&recursor_name).cloned() else {
        return Err(unsupported(&family.base.name));
    };
    if metadata.is_unsafe
        || metadata.num_motives != 1
        || metadata.num_indices != family.num_indices
        || metadata.num_params != family.num_params
        || metadata.num_minors as usize != family.ctors.len()
        || metadata.rules.len() != family.ctors.len()
        || metadata.all != family.all
    {
        return Err(unsupported(&family.base.name));
    }
    let result_type = Expr::const_(named("UInt64"), Vec::new());
    let mut function = context.constant(&recursor_name)?;
    for parameter in parameters {
        function = context.match_apply(function, value(parameter))?;
    }
    let mut motive = Expr::lam(
        Name::anonymous(),
        target.clone(),
        result_type.clone(),
        BinderInfo::Default,
    );
    for index in indices.iter().rev() {
        context.tick()?;
        motive = Expr::lam(
            index.user_name.clone(),
            index.type_.clone(),
            motive
                .abstract_fvar(&index.id, 0)
                .map_err(|_| failure(SourceInferenceError::Scope))?,
            index.binder_info,
        );
    }
    let motive = typed(context, motive)?;
    function = context.match_apply(function, motive)?;
    for rule in &metadata.rules {
        context.tick()?;
        let Some(ConstantInfo::Ctor(constructor)) = context.txn.env.find(&rule.ctor).cloned()
        else {
            return Err(unsupported(&family.base.name));
        };
        let Some(index) = family.ctors.iter().position(|name| name == &rule.ctor) else {
            return Err(unsupported(&family.base.name));
        };
        if constructor.is_unsafe
            || constructor.induct != family.base.name
            || constructor.num_params != family.num_params
            || constructor.num_fields != rule.nfields
        {
            return Err(unsupported(&family.base.name));
        }
        if constructor.num_fields as usize > crate::records::RecordBudget::default().max_binders {
            return Err(failure(SourceInferenceError::ResourceLimit));
        }
        let function_type = context.whnf(&function.type_)?;
        let ExprNode::ForallE { binder_type, .. } = function_type.node() else {
            return Err(unsupported(&family.base.name));
        };
        let saved = context.txn.lctx.clone();
        let mut cursor = binder_type.clone();
        let recursive = context.constructor_recursive_fields(&constructor)?;
        let mut fields = Vec::new();
        for _ in 0..constructor.num_fields {
            fields.push(open_binder(context, &mut cursor)?);
        }
        let mut binders = fields.clone();
        let mut hypotheses = Vec::new();
        for (field, recursive) in fields.iter().zip(recursive) {
            context.tick()?;
            if recursive {
                let domain = context.whnf(&field.type_)?;
                let mut head = &domain;
                while let ExprNode::App { f, .. } = head.node() {
                    context.tick()?;
                    head = f;
                }
                // The pin selects direct recursive calls from the WHNF head.
                // A function's IH hashes its results, not the function itself.
                if !matches!(head.node(), ExprNode::Const { name, .. } if name == &family.base.name)
                {
                    return Err(unsupported(&family.base.name));
                }
                let hypothesis = open_binder(context, &mut cursor)?;
                context.constrain_type(&hypothesis.type_, &result_type)?;
                binders.push(hypothesis.clone());
                hypotheses.push(Some(hypothesis));
            } else {
                hypotheses.push(None);
            }
        }
        context.constrain_type(&cursor, &result_type)?;
        let mut body = ordinal(context, index)?;
        for (field, hypothesis) in fields.iter().zip(&hypotheses) {
            context.tick()?;
            let hash = match hypothesis {
                Some(hypothesis) => value(hypothesis),
                None => hash_field(context, field)?,
            };
            body = call(context, "mixHash", &[body, hash])?;
        }
        context.constrain_type(&body.type_, &cursor)?;
        let branch = bind(context, body, &binders)?;
        function = context.match_apply(function, branch)?;
        context.txn.lctx = saved;
    }
    for index in indices {
        function = context.match_apply(function, value(index))?;
    }
    let mut result = context.match_apply(function, value(receiver))?;
    // The recursor initially leaves its motive applied to the receiver in
    // the inferred codomain. Publish the pin's ordinary UInt64 helper header,
    // after checking that this is the same type, rather than a beta-redex.
    context.constrain_type(&result.type_, &result_type)?;
    result.type_ = result_type;
    Ok(result)
}

pub(super) fn elaborate(
    context: &mut Context,
    family: &InductiveVal,
    parameters: &[LocalDecl],
    target: &Expr,
) -> Result<DerivedInstance, NatDefinitionElabError> {
    check_exposure(context, family)?;
    // Nested/mutual derivation needs the pin's local recursive dictionaries and
    // partial-function admission. Never substitute a nonrecursive dictionary.
    if family.all.len() != 1 || family.num_nested != 0 {
        return Err(unsupported(&family.base.name));
    }
    let (indices, target) = family_indices(context, family, target)?;
    let class = class_type(context, &target)?;
    let mut header = parameters.to_vec();
    header.extend(indices.iter().cloned());
    let instance = context.generated_instance_name(&header, &class.value)?;
    let helper = Name::str(instance.clone(), "hash");
    // The pin retains every type-correct parameter dictionary, including
    // phantom parameters and propositions. Indices receive no dictionaries.
    for (index, parameter) in parameters.iter().enumerate() {
        if !matches!(
            context.whnf(&parameter.type_)?.node(),
            ExprNode::Sort { .. }
        ) {
            continue;
        }
        let mut trial = context.clone();
        let result = class_type(&mut trial, &Expr::fvar(parameter.id.clone()));
        context.txn.budget.heartbeats_consumed = trial.txn.budget.heartbeats_consumed;
        match result {
            Ok(class) => {
                *context = trial;
                header.push(local(
                    context,
                    named(&format!("inst{index}")),
                    class.value,
                    BinderInfo::InstImplicit,
                )?);
            }
            Err(error) if normal_failure(&error) => {}
            Err(error) => return Err(error),
        }
    }
    let receiver = local(context, named("x"), target.clone(), BinderInfo::Default)?;
    let body = hash_body(context, family, parameters, &indices, &target, &receiver)?;
    let mut helper_header = header.clone();
    helper_header.push(receiver);
    let helper_term = close(context, body, &helper_header)?;
    let levels = family
        .base
        .level_params
        .iter()
        .cloned()
        .map(Level::param)
        .collect();
    let mut helper_call = Typed {
        value: Expr::const_(helper.clone(), levels),
        type_: helper_term.type_.clone(),
    };
    for parameter in &header {
        helper_call = context.match_apply(helper_call, value(parameter))?;
    }
    let carrier = typed(context, target)?;
    let dictionary = call(context, "Hashable.mk", &[carrier, helper_call])?;
    context.constrain_type(&dictionary.type_, &class.value)?;
    let instance_term = close(context, dictionary, &header)?;
    let definition = |name: Name, term: Typed| {
        Declaration::Defn(DefinitionVal {
            base: ConstantVal {
                name: name.clone(),
                level_params: family.base.level_params.clone(),
                type_: term.type_,
            },
            value: term.value,
            hints: ReducibilityHints::Regular(1),
            safety: DefinitionSafety::Safe,
            all: vec![name],
        })
    };
    Ok(DerivedInstance {
        declarations: vec![
            definition(helper, helper_term),
            definition(instance.clone(), instance_term),
        ],
        instance,
    })
}
