//! Native ordering for nonrecursive algebraic data, built from checked recursors.
//!
//! The pin's Deriving/Ord.lean orders constructors and compares their non-proof
//! fields lexicographically. Its enum path compares constructor indices through
//! the active Ord Nat dictionary. Recursive, nested and mutual families need
//! the pin's partial helpers; they remain refused rather than becoming
//! transparently reducible through a different logical implementation.
use super::*;
use fln_env::constants::{ConstructorVal, RecursorVal};

fn typed(context: &mut Context, value: Expr) -> Result<Typed, NatDefinitionElabError> {
    let type_ = context
        .known_type(&value)?
        .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
    Ok(Typed { value, type_ })
}

fn call(
    context: &mut Context,
    name: &Name,
    arguments: &[Typed],
) -> Result<Typed, NatDefinitionElabError> {
    let mut function = context.constant(name)?;
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

fn ordering() -> Expr {
    Expr::const_(named("Ordering"), Vec::new())
}

fn class_type(context: &mut Context, carrier: &Expr) -> Result<Typed, NatDefinitionElabError> {
    let carrier = typed(context, carrier.clone())?;
    let class = call(context, &named("Ord"), &[carrier])?;
    context.finish(class)
}

fn compare(
    context: &mut Context,
    left: Typed,
    right: Typed,
) -> Result<Typed, NatDefinitionElabError> {
    // Dependent data fields are not identified by the result of a comparison.
    // Their types must agree before a single dictionary can compare them.
    context.constrain_type(&left.type_, &right.type_)?;
    let class = class_type(context, &left.type_)?;
    let dictionary = context.instance_hole(class.value.clone())?;
    context.resolve_instances(true)?;
    let dictionary = Typed {
        value: context.instantiate(&dictionary)?,
        type_: class.value,
    };
    let carrier = typed(context, left.type_.clone())?;
    call(
        context,
        &named("Ord.compare"),
        &[carrier, dictionary, left, right],
    )
}

/// The checked eliminator implementing Ordering.then. Keeping the next
/// comparison in its eq branch preserves lexicographic short-circuiting.
fn then(context: &mut Context, first: Typed, next: Typed) -> Result<Typed, NatDefinitionElabError> {
    let recursor = named("Ordering.rec");
    let Some(ConstantInfo::Rec(metadata)) = context.txn.env.find(&recursor).cloned() else {
        return Err(unsupported(&named("Ordering")));
    };
    if metadata.num_params != 0
        || metadata.num_indices != 0
        || metadata.num_motives != 1
        || metadata.num_minors != 3
        || metadata.rules.len() != 3
    {
        return Err(unsupported(&named("Ordering")));
    }
    let motive = typed(
        context,
        Expr::lam(
            Name::anonymous(),
            ordering(),
            ordering(),
            BinderInfo::Default,
        ),
    )?;
    let mut function = call(context, &recursor, &[motive])?;
    for rule in &metadata.rules {
        context.tick()?;
        if rule.nfields != 0 {
            return Err(unsupported(&named("Ordering")));
        }
        let branch = if rule.ctor == named("Ordering.eq") {
            next.clone()
        } else if rule.ctor == named("Ordering.lt") || rule.ctor == named("Ordering.gt") {
            context.constant(&rule.ctor)?
        } else {
            return Err(unsupported(&named("Ordering")));
        };
        function = context.match_apply(function, branch)?;
    }
    context.match_apply(function, first)
}

struct Minor {
    ordinal: u32,
    fields: Vec<LocalDecl>,
    result: Expr,
}

fn constructor(
    context: &mut Context,
    family: &InductiveVal,
    name: &Name,
    nfields: u32,
) -> Result<ConstructorVal, NatDefinitionElabError> {
    let Some(ConstantInfo::Ctor(constructor)) = context.txn.env.find(name).cloned() else {
        return Err(unsupported(&family.base.name));
    };
    if constructor.is_unsafe
        || constructor.induct != family.base.name
        || constructor.num_params != family.num_params
        || constructor.num_fields != nfields
        || family.ctors.get(constructor.cidx as usize) != Some(name)
    {
        return Err(unsupported(&family.base.name));
    }
    Ok(constructor)
}

fn open_minor(
    context: &mut Context,
    constructor: &ConstructorVal,
    result: &Expr,
    type_: &Expr,
) -> Result<Minor, NatDefinitionElabError> {
    if constructor.num_fields as usize > crate::records::RecordBudget::default().max_binders {
        return Err(failure(SourceInferenceError::ResourceLimit));
    }
    let mut cursor = type_.clone();
    let mut fields = Vec::new();
    for _ in 0..constructor.num_fields {
        fields.push(open_binder(context, &mut cursor)?);
    }
    // No recursive hypotheses are silently dropped. The caller refuses
    // recursive families before reaching this nonrecursive telescope.
    context.constrain_type(&cursor, result)?;
    Ok(Minor {
        ordinal: constructor.cidx,
        fields,
        result: cursor,
    })
}

fn recursor(
    context: &mut Context,
    family: &InductiveVal,
    parameters: &[LocalDecl],
    target: &Expr,
    result: Expr,
) -> Result<Typed, NatDefinitionElabError> {
    let mut function = context.constant(&Name::str(family.base.name.clone(), "rec"))?;
    for parameter in parameters {
        function = context.match_apply(function, value(parameter))?;
    }
    let motive = typed(
        context,
        Expr::lam(
            Name::anonymous(),
            target.clone(),
            result,
            BinderInfo::Default,
        ),
    )?;
    context.match_apply(function, motive)
}

fn minor_type(context: &mut Context, function: &Typed) -> Result<Expr, NatDefinitionElabError> {
    let type_ = context.whnf(&function.type_)?;
    let ExprNode::ForallE { binder_type, .. } = type_.node() else {
        return Err(failure(SourceInferenceError::ExpectedFunction));
    };
    Ok(binder_type.clone())
}

fn compare_constructor(
    context: &mut Context,
    family: &InductiveVal,
    metadata: &RecursorVal,
    parameters: &[LocalDecl],
    target: &Expr,
    left: &Minor,
    right: &LocalDecl,
) -> Result<Typed, NatDefinitionElabError> {
    let mut function = recursor(context, family, parameters, target, ordering())?;
    for rule in &metadata.rules {
        context.tick()?;
        let constructor = constructor(context, family, &rule.ctor, rule.nfields)?;
        let type_ = minor_type(context, &function)?;
        let saved = context.txn.lctx.clone();
        let branch = open_minor(context, &constructor, &ordering(), &type_)?;
        let body = match left.ordinal.cmp(&branch.ordinal) {
            std::cmp::Ordering::Less => context.constant(&named("Ordering.lt"))?,
            std::cmp::Ordering::Greater => context.constant(&named("Ordering.gt"))?,
            std::cmp::Ordering::Equal => {
                let mut comparisons = Vec::new();
                for (index, field) in left.fields.iter().enumerate() {
                    context.tick()?;
                    let sort = context
                        .known_type(&field.type_)?
                        .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
                    if matches!(context.whnf(&sort)?.node(), ExprNode::Sort { level } if level.is_zero())
                    {
                        continue;
                    }
                    let rhs = branch
                        .fields
                        .get(index)
                        .ok_or_else(|| unsupported(&family.base.name))?;
                    comparisons.push(compare(context, value(field), value(rhs))?);
                }
                // The final eq is part of the pin's generated term, including
                // when the last field's comparison itself remains symbolic.
                let mut body = context.constant(&named("Ordering.eq"))?;
                while let Some(comparison) = comparisons.pop() {
                    body = then(context, comparison, body)?;
                }
                body
            }
        };
        context.constrain_type(&body.type_, &branch.result)?;
        let branch = bind(context, body, &branch.fields)?;
        function = context.match_apply(function, branch)?;
        context.txn.lctx = saved;
    }
    context.match_apply(function, value(right))
}

fn is_enum(context: &mut Context, family: &InductiveVal) -> Result<bool, NatDefinitionElabError> {
    if family.num_params != 0 || family.ctors.is_empty() {
        return Ok(false);
    }
    for name in &family.ctors {
        context.tick()?;
        if !matches!(context.txn.env.find(name), Some(ConstantInfo::Ctor(ctor)) if ctor.num_fields == 0)
        {
            return Ok(false);
        }
    }
    Ok(true)
}

pub(super) fn elaborate(
    context: &mut Context,
    family: &InductiveVal,
    parameters: &[LocalDecl],
    target: &Expr,
) -> Result<DerivedInstance, NatDefinitionElabError> {
    check_exposure(context, family)?;
    if family.is_rec
        || family.num_indices != 0
        || family.all.len() != 1
        || family.num_nested != 0
    {
        return Err(unsupported(&family.base.name));
    }
    let recursor_name = Name::str(family.base.name.clone(), "rec");
    let Some(ConstantInfo::Rec(metadata)) = context.txn.env.find(&recursor_name).cloned() else {
        return Err(unsupported(&family.base.name));
    };
    if metadata.is_unsafe
        || metadata.num_motives != 1
        || metadata.num_indices != 0
        || metadata.num_params != family.num_params
        || metadata.num_minors as usize != family.ctors.len()
        || metadata.rules.len() != family.ctors.len()
        || metadata.all != family.all
    {
        return Err(unsupported(&family.base.name));
    }
    let enum_type = is_enum(context, family)?;
    // The pin switches non-enums to mkCasesOnSameCtor at this threshold.
    // That path has its own constructor-index dictionary and equality proof;
    // do not silently replace it with the small-family construction.
    if !enum_type && family.ctors.len() >= 10 {
        return Err(unsupported(&family.base.name));
    }
    let class = class_type(context, target)?;
    let instance = context.generated_instance_name(parameters, &class.value)?;
    let helper = Name::str(instance.clone(), "ord");
    let mut header = parameters.to_vec();
    // Deriving.Util.mkHeader retains every type-correct parameter dictionary,
    // including a phantom parameter. The actual fields use these local instances.
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
    let left = local(context, named("x"), target.clone(), BinderInfo::Default)?;
    let right = local(context, named("y"), target.clone(), BinderInfo::Default)?;
    let body = if enum_type {
        // The pin does not hard-code the enum's ordering: a scoped Ord Nat can
        // change the comparison of its constructor indices at derivation time.
        let index = Name::str(family.base.name.clone(), "ctorIdx");
        let first = call(context, &index, &[value(&left)])?;
        let second = call(context, &index, &[value(&right)])?;
        compare(context, first, second)?
    } else {
        let result = Expr::forall_e(
            Name::anonymous(),
            target.clone(),
            ordering(),
            BinderInfo::Default,
        );
        let mut function = recursor(context, family, parameters, target, result.clone())?;
        for rule in &metadata.rules {
            context.tick()?;
            let constructor = constructor(context, family, &rule.ctor, rule.nfields)?;
            let type_ = minor_type(context, &function)?;
            let saved = context.txn.lctx.clone();
            let mut branch = open_minor(context, &constructor, &result, &type_)?;
            let receiver = open_binder(context, &mut branch.result)?;
            context.constrain_type(&receiver.type_, target)?;
            let body = compare_constructor(
                context, family, &metadata, parameters, target, &branch, &receiver,
            )?;
            context.constrain_type(&body.type_, &branch.result)?;
            branch.fields.push(receiver);
            let branch = bind(context, body, &branch.fields)?;
            function = context.match_apply(function, branch)?;
            context.txn.lctx = saved;
        }
        let function = context.match_apply(function, value(&left))?;
        context.match_apply(function, value(&right))?
    };
    let mut helper_header = header.clone();
    helper_header.extend([left, right]);
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
    let dictionary = call(context, &named("Ord.mk"), &[carrier, helper_call])?;
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
