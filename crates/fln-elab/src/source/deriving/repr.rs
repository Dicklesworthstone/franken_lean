//! Native construction of the pin's Repr helper and dictionary. Formatting is
//! ordinary checked library code, including the actual Format layout functions.
use super::*;
use fln_env::constants::ConstructorVal;

fn typed(context: &mut Context, value: Expr) -> Result<Typed, NatDefinitionElabError> {
    let type_ = context
        .known_type(&value)?
        .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
    Ok(Typed { value, type_ })
}

fn call(
    context: &mut Context,
    function: &str,
    arguments: &[Typed],
) -> Result<Typed, NatDefinitionElabError> {
    let mut term = context.constant(&named(function))?;
    for argument in arguments {
        term = context.match_apply(term, argument.clone())?;
    }
    Ok(term)
}

fn nat(value: u64) -> Typed {
    Typed {
        value: Expr::lit(Literal::Nat(fln_core::expr::NatLit::from_u64(value))),
        type_: nat_const(),
    }
}

fn string(value: &str) -> Typed {
    Typed {
        value: Expr::lit(Literal::Str(value.to_owned())),
        type_: string_const(),
    }
}

fn text(context: &mut Context, value: &str) -> Result<Typed, NatDefinitionElabError> {
    call(context, "Std.Format.text", &[string(value)])
}

fn append(
    context: &mut Context,
    left: Typed,
    right: Typed,
) -> Result<Typed, NatDefinitionElabError> {
    call(context, "Std.Format.append", &[left, right])
}

fn group(context: &mut Context, format: Typed) -> Result<Typed, NatDefinitionElabError> {
    let behavior = context.constant(&named("Std.Format.FlattenBehavior.allOrNone"))?;
    call(context, "Std.Format.group", &[format, behavior])
}

fn nest(
    context: &mut Context,
    indentation: Typed,
    format: Typed,
) -> Result<Typed, NatDefinitionElabError> {
    call(context, "Std.Format.nest", &[indentation, format])
}

fn local(
    context: &mut Context,
    name: Name,
    type_: Expr,
    style: BinderInfo,
) -> Result<LocalDecl, NatDefinitionElabError> {
    let id = FVarId(context.fresh_name()?);
    Ok(context.txn.lctx.add_param(id, name, type_, style).clone())
}

fn value(local: &LocalDecl) -> Typed {
    Typed {
        value: Expr::fvar(local.id.clone()),
        type_: local.type_.clone(),
    }
}

/// Close a branch while retaining its surrounding helper parameters.
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
    let target = call(context, "Repr", &[carrier])?;
    context.finish(target)
}

fn erased(context: &mut Context, field: &Typed) -> Result<bool, NatDefinitionElabError> {
    if matches!(context.whnf(&field.type_)?.node(), ExprNode::Sort { .. }) {
        return Ok(true);
    }
    let sort = context
        .known_type(&field.type_)?
        .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
    Ok(matches!(context.whnf(&sort)?.node(), ExprNode::Sort { level } if level.is_zero()))
}

fn repr(
    context: &mut Context,
    field: Typed,
    precedence: Typed,
) -> Result<Typed, NatDefinitionElabError> {
    if erased(context, &field)? {
        return text(context, "_");
    }
    let class = class_type(context, &field.type_)?;
    let dictionary = context.instance_hole(class.value.clone())?;
    context.resolve_instances(true)?;
    let dictionary = Typed {
        value: context.instantiate(&dictionary)?,
        type_: class.value,
    };
    let carrier = typed(context, field.type_.clone())?;
    call(
        context,
        "Repr.reprPrec",
        &[carrier, dictionary, field, precedence],
    )
}

fn record_body(
    context: &mut Context,
    family: &InductiveVal,
    parameters: &[LocalDecl],
    receiver: &LocalDecl,
) -> Result<Typed, NatDefinitionElabError> {
    if family.ctors.len() != 1 {
        return Err(unsupported(&family.base.name));
    }
    let Some(ConstantInfo::Ctor(constructor)) = context.txn.env.find(&family.ctors[0]).cloned()
    else {
        return Err(unsupported(&family.base.name));
    };
    let levels: Vec<_> = family
        .base
        .level_params
        .iter()
        .cloned()
        .map(Level::param)
        .collect();
    let mut cursor = context.instantiate_params(
        &constructor.base.type_,
        &constructor.base.level_params,
        &levels,
    )?;
    for parameter in parameters {
        let normalized = context.whnf(&cursor)?;
        let ExprNode::ForallE { body, .. } = normalized.node() else {
            return Err(unsupported(&family.base.name));
        };
        cursor = context.substitute(body, &Expr::fvar(parameter.id.clone()))?;
    }
    if constructor.num_fields as usize > crate::records::RecordBudget::default().max_binders {
        return Err(failure(SourceInferenceError::ResourceLimit));
    }
    let mut result = context.constant(&named("Std.Format.nil"))?;
    for index in 0..constructor.num_fields {
        context.tick()?;
        let normalized = context.whnf(&cursor)?;
        let ExprNode::ForallE {
            binder_name,
            binder_type,
            body,
            ..
        } = normalized.node()
        else {
            return Err(unsupported(&family.base.name));
        };
        let field = Typed {
            value: Expr::proj(
                family.base.name.clone(),
                u64::from(index),
                Expr::fvar(receiver.id.clone()),
            ),
            type_: binder_type.clone(),
        };
        cursor = context.substitute(body, &field.value)?;
        if index != 0 {
            let comma = text(context, ",")?;
            result = append(context, result, comma)?;
            let line = context.constant(&named("Std.Format.line"))?;
            result = append(context, result, line)?;
        }
        let label = binder_name.to_display_string();
        let label_format = text(context, &label)?;
        result = append(context, result, label_format)?;
        let assignment = text(context, " := ")?;
        result = append(context, result, assignment)?;
        let rendered = if erased(context, &field)? {
            text(context, "_")?
        } else {
            let rendered = repr(context, field, nat(0))?;
            let indentation = call(
                context,
                "Int.ofNat",
                &[nat(label.chars().count() as u64 + 4)],
            )?;
            let rendered = nest(context, indentation, rendered)?;
            group(context, rendered)?
        };
        result = append(context, result, rendered)?;
    }
    call(
        context,
        "Std.Format.bracket",
        &[string("{ "), result, string(" }")],
    )
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

fn inductive_format(
    context: &mut Context,
    constructor: &ConstructorVal,
    parameters: &[LocalDecl],
    fields: &[LocalDecl],
    precedence: &LocalDecl,
) -> Result<Typed, NatDefinitionElabError> {
    let mut result = text(context, &constructor.base.name.to_display_string())?;
    let mut arguments = Vec::new();
    let mut constructor_type = &constructor.base.type_;
    for parameter in parameters {
        context.tick()?;
        let ExprNode::ForallE {
            binder_info, body, ..
        } = constructor_type.node()
        else {
            return Err(unsupported(&constructor.induct));
        };
        // Fixed indices promoted to parameters retain their explicit
        // constructor binders. They are still visible arguments in the pin.
        if *binder_info == BinderInfo::Default {
            arguments.push(value(parameter));
        }
        constructor_type = body;
    }
    arguments.extend(
        fields
            .iter()
            .filter(|field| field.binder_info == BinderInfo::Default)
            .map(value),
    );
    for field in arguments {
        context.tick()?;
        let line = context.constant(&named("Std.Format.line"))?;
        result = append(context, result, line)?;
        // Init.Notation's max_prec macro expands to 1024.
        let field = repr(context, field, nat(1024))?;
        result = append(context, result, field)?;
    }
    let high = call(context, "Nat.ble", &[nat(1024), value(precedence)])?;
    let one = call(context, "Int.ofNat", &[nat(1)])?;
    let two = call(context, "Int.ofNat", &[nat(2)])?;
    let int_type = Expr::const_(named("Int"), Vec::new());
    let motive = typed(
        context,
        Expr::lam(
            Name::anonymous(),
            Expr::const_(named("Bool"), Vec::new()),
            int_type,
            BinderInfo::Default,
        ),
    )?;
    let indentation = call(context, "Bool.rec", &[motive, two, one, high])?;
    let result = nest(context, indentation, result)?;
    let result = group(context, result)?;
    call(context, "Repr.addAppParen", &[result, value(precedence)])
}

fn inductive_body(
    context: &mut Context,
    family: &InductiveVal,
    parameters: &[LocalDecl],
    target: &Expr,
    receiver: &LocalDecl,
    precedence: &LocalDecl,
) -> Result<Typed, NatDefinitionElabError> {
    let recursor_name = Name::str(family.base.name.clone(), "rec");
    let Some(ConstantInfo::Rec(recursor)) = context.txn.env.find(&recursor_name).cloned() else {
        return Err(unsupported(&family.base.name));
    };
    if recursor.is_unsafe
        || recursor.num_motives != 1
        || recursor.num_indices != 0
        || recursor.num_params != family.num_params
        || recursor.num_minors as usize != family.ctors.len()
        || recursor.rules.len() != family.ctors.len()
        || recursor.all != family.all
    {
        return Err(unsupported(&family.base.name));
    }
    let mut function = context.constant(&recursor_name)?;
    for parameter in parameters {
        function = context.match_apply(function, value(parameter))?;
    }
    let result_type = Expr::forall_e(
        named("prec"),
        nat_const(),
        Expr::const_(named("Std.Format"), Vec::new()),
        BinderInfo::Default,
    );
    let motive = typed(
        context,
        Expr::lam(
            Name::anonymous(),
            target.clone(),
            result_type,
            BinderInfo::Default,
        ),
    )?;
    function = context.match_apply(function, motive)?;
    for rule in &recursor.rules {
        context.tick()?;
        let Some(ConstantInfo::Ctor(constructor)) = context.txn.env.find(&rule.ctor).cloned()
        else {
            return Err(unsupported(&family.base.name));
        };
        if constructor.is_unsafe
            || constructor.induct != family.base.name
            || constructor.num_params != family.num_params
            || constructor.num_fields != rule.nfields
            || !family.ctors.contains(&rule.ctor)
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
        let mut fields = Vec::new();
        for _ in 0..constructor.num_fields {
            fields.push(open_binder(context, &mut cursor)?);
        }
        let prec = open_binder(context, &mut cursor)?;
        let format = inductive_format(context, &constructor, parameters, &fields, &prec)?;
        context.constrain_type(&format.type_, &cursor)?;
        fields.push(prec);
        let branch = bind(context, format, &fields)?;
        function = context.match_apply(function, branch)?;
        context.txn.lctx = saved;
    }
    function = context.match_apply(function, value(receiver))?;
    context.match_apply(function, value(precedence))
}

pub(super) fn elaborate(
    context: &mut Context,
    family: &InductiveVal,
    parameters: &[LocalDecl],
    target: &Expr,
    is_record: bool,
) -> Result<DerivedInstance, NatDefinitionElabError> {
    if family.all.len() != 1 || family.num_nested != 0 || family.is_rec {
        return Err(unsupported(&family.base.name));
    }
    let mut parameter_type = &family.base.type_;
    for _ in parameters {
        context.tick()?;
        let ExprNode::ForallE {
            binder_info, body, ..
        } = parameter_type.node()
        else {
            return Err(unsupported(&family.base.name));
        };
        // The pin re-elaborates projection receivers with its fresh instance
        // binders. A family's existing dictionary may conflict with those;
        // direct kernel projections must not bypass that source refusal.
        if *binder_info == BinderInfo::InstImplicit {
            return Err(unsupported(&family.base.name));
        }
        parameter_type = body;
    }
    let class = class_type(context, target)?;
    let instance = context.generated_instance_name(parameters, &class.value)?;
    let helper = Name::str(instance.clone(), "repr");
    let mut header = parameters.to_vec();
    // Unlike Inhabited, the pin's generic Repr handler retains every
    // well-typed parameter hypothesis, even when no field uses it.
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
    let precedence = local(context, named("prec"), nat_const(), BinderInfo::Default)?;
    let body = if is_record {
        record_body(context, family, parameters, &receiver)?
    } else {
        inductive_body(context, family, parameters, target, &receiver, &precedence)?
    };
    let mut helper_header = header.clone();
    helper_header.extend([receiver, precedence]);
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
    let carrier = typed(context, target.clone())?;
    let dictionary = call(context, "Repr.mk", &[carrier, helper_call])?;
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
