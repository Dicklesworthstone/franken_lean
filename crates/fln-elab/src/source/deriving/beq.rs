//! Boolean equality for ordinary algebraic data, built from checked recursors.
//!
//! The pinned `Deriving/BEq.lean` compares matching constructors field by field,
//! ignores proofs, and recursively compares immediate recursive children. The
//! outer motive is `Family -> Bool`: its induction hypotheses are the equality
//! functions for the left-hand children, never unconstrained recursive calls.
//! Parameter hypotheses and generated names follow `Deriving/Util.lean`.
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

/// Branch closure leaves the enclosing helper's parameters in its context.
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

fn bool_type() -> Expr {
    Expr::const_(named("Bool"), Vec::new())
}

fn comparison_type(target: &Expr) -> Expr {
    Expr::forall_e(
        Name::anonymous(),
        target.clone(),
        bool_type(),
        BinderInfo::Default,
    )
}

fn class_type(context: &mut Context, carrier: &Expr) -> Result<Typed, NatDefinitionElabError> {
    let carrier = typed(context, carrier.clone())?;
    let class = call(context, "BEq", &[carrier])?;
    context.finish(class)
}

fn is_proof(context: &mut Context, field: &LocalDecl) -> Result<bool, NatDefinitionElabError> {
    let sort = context
        .known_type(&field.type_)?
        .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
    Ok(matches!(context.whnf(&sort)?.node(), ExprNode::Sort { level } if level.is_zero()))
}

fn compare(
    context: &mut Context,
    left: &LocalDecl,
    right: &LocalDecl,
    hypothesis: Option<&LocalDecl>,
) -> Result<Typed, NatDefinitionElabError> {
    // Dependent data fields require the pin's LawfulBEq transport. Do not erase
    // their different types or treat a Boolean comparison as a proof of Eq.
    context.constrain_type(&left.type_, &right.type_)?;
    if let Some(hypothesis) = hypothesis {
        return context.match_apply(value(hypothesis), value(right));
    }
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
        "BEq.beq",
        &[carrier, dictionary, value(left), value(right)],
    )
}

/// This is the checked Bool eliminator underlying the pin's `&&`. The source
/// seed need not contain an independently installed notation implementation.
fn and(context: &mut Context, left: Typed, right: Typed) -> Result<Typed, NatDefinitionElabError> {
    let motive = typed(
        context,
        Expr::lam(
            Name::anonymous(),
            bool_type(),
            bool_type(),
            BinderInfo::Default,
        ),
    )?;
    let no = context.constant(&named("Bool.false"))?;
    call(context, "Bool.rec", &[motive, no, right, left])
}

struct Minor {
    constructor: Name,
    fields: Vec<LocalDecl>,
    hypotheses: Vec<Option<LocalDecl>>,
    binders: Vec<LocalDecl>,
    result: Expr,
}

/// Read the checked recursor's own telescope. The supported recursion shape is
/// an immediate child of this same family with its fixed parameters unchanged.
fn open_minor(
    context: &mut Context,
    family: &InductiveVal,
    constructor: &ConstructorVal,
    target: &Expr,
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
    let mut binders = fields.clone();
    let mut hypotheses = Vec::new();
    for field in &fields {
        context.tick()?;
        let type_ = context.whnf(&field.type_)?;
        let mut head = &type_;
        while let ExprNode::App { f, .. } = head.node() {
            context.tick()?;
            head = f;
        }
        if matches!(head.node(), ExprNode::Const { name, .. } if name == &family.base.name) {
            context.constrain_type(&field.type_, target)?;
            let hypothesis = open_binder(context, &mut cursor)?;
            context.constrain_type(&hypothesis.type_, result)?;
            binders.push(hypothesis.clone());
            hypotheses.push(Some(hypothesis));
        } else {
            hypotheses.push(None);
        }
    }
    // A function-valued recursive field has an additional IH that cannot be
    // consumed as ordinary field equality. This constraint leaves it refused.
    context.constrain_type(&cursor, result)?;
    Ok(Minor {
        constructor: constructor.base.name.clone(),
        fields,
        hypotheses,
        binders,
        result: cursor,
    })
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
        || !family.ctors.contains(name)
    {
        return Err(unsupported(&family.base.name));
    }
    Ok(constructor)
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
    let mut function = recursor(context, family, parameters, target, bool_type())?;
    for rule in &metadata.rules {
        context.tick()?;
        let constructor = constructor(context, family, &rule.ctor, rule.nfields)?;
        let type_ = minor_type(context, &function)?;
        let saved = context.txn.lctx.clone();
        let branch = open_minor(context, family, &constructor, target, &bool_type(), &type_)?;
        let body = if rule.ctor == left.constructor {
            let mut comparisons = Vec::new();
            for (index, field) in left.fields.iter().enumerate() {
                context.tick()?;
                if is_proof(context, field)? {
                    continue;
                }
                let rhs = branch
                    .fields
                    .get(index)
                    .ok_or_else(|| unsupported(&family.base.name))?;
                comparisons.push(compare(
                    context,
                    field,
                    rhs,
                    left.hypotheses[index].as_ref(),
                )?);
            }
            let mut body = match comparisons.pop() {
                Some(comparison) => comparison,
                None => context.constant(&named("Bool.true"))?,
            };
            while let Some(comparison) = comparisons.pop() {
                body = and(context, comparison, body)?;
            }
            body
        } else {
            context.constant(&named("Bool.false"))?
        };
        context.constrain_type(&body.type_, &branch.result)?;
        let branch = bind(context, body, &branch.binders)?;
        function = context.match_apply(function, branch)?;
        context.txn.lctx = saved;
    }
    context.match_apply(function, value(right))
}

pub(super) fn elaborate(
    context: &mut Context,
    family: &InductiveVal,
    parameters: &[LocalDecl],
    target: &Expr,
) -> Result<DerivedInstance, NatDefinitionElabError> {
    if family.all.len() != 1 || family.num_nested != 0 {
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
    let class = class_type(context, target)?;
    let instance = context.generated_instance_name(parameters, &class.value)?;
    let helper = Name::str(instance.clone(), "beq");
    let mut header = parameters.to_vec();
    // The pin retains every well-typed BEq parameter hypothesis, even if no
    // constructor field uses that parameter (Deriving.Util.mkHeader).
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
    let result = comparison_type(target);
    let mut function = recursor(context, family, parameters, target, result.clone())?;
    for rule in &metadata.rules {
        context.tick()?;
        let constructor = constructor(context, family, &rule.ctor, rule.nfields)?;
        let type_ = minor_type(context, &function)?;
        let saved = context.txn.lctx.clone();
        let mut branch = open_minor(context, family, &constructor, target, &result, &type_)?;
        let receiver = open_binder(context, &mut branch.result)?;
        context.constrain_type(&receiver.type_, target)?;
        let body = compare_constructor(
            context, family, &metadata, parameters, target, &branch, &receiver,
        )?;
        context.constrain_type(&body.type_, &branch.result)?;
        branch.binders.push(receiver);
        let branch = bind(context, body, &branch.binders)?;
        function = context.match_apply(function, branch)?;
        context.txn.lctx = saved;
    }
    let body = context.match_apply(function, value(&left))?;
    let body = context.match_apply(body, value(&right))?;
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
    let dictionary = call(context, "BEq.mk", &[carrier, helper_call])?;
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
