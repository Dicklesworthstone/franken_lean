//! Proof-producing DecidableEq for single, nonindexed algebraic families.
//!
//! Recursion uses the admitted recursor's hypotheses. A failed field decision
//! is refuted by checked constructor injection; a successful decision transports
//! the remaining constructor telescope through Eq.rec. Boolean equality is
//! never used as equality evidence, and no auxiliary axiom is admitted.
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

fn value(local: &LocalDecl) -> Typed {
    Typed {
        value: Expr::fvar(local.id.clone()),
        type_: local.type_.clone(),
    }
}

fn local(
    context: &mut Context,
    name: Name,
    type_: Expr,
    info: BinderInfo,
) -> Result<LocalDecl, NatDefinitionElabError> {
    let id = FVarId(context.fresh_name()?);
    Ok(context.txn.lctx.add_param(id, name, type_, info).clone())
}

fn open_binder(
    context: &mut Context,
    cursor: &mut Expr,
) -> Result<LocalDecl, NatDefinitionElabError> {
    let type_ = context.whnf(cursor)?;
    let ExprNode::ForallE {
        binder_name,
        binder_type,
        body,
        binder_info,
    } = type_.node()
    else {
        return Err(failure(SourceInferenceError::ExpectedFunction));
    };
    let result = local(
        context,
        binder_name.clone(),
        binder_type.clone(),
        *binder_info,
    )?;
    *cursor = context.substitute(body, &Expr::fvar(result.id.clone()))?;
    Ok(result)
}

fn forall(
    context: &mut Context,
    mut type_: Expr,
    locals: &[LocalDecl],
) -> Result<Expr, NatDefinitionElabError> {
    for local in locals.iter().rev() {
        context.tick()?;
        type_ = Expr::forall_e(
            local.user_name.clone(),
            context.instantiate(&local.type_)?,
            type_
                .abstract_fvar(&local.id, 0)
                .map_err(|_| failure(SourceInferenceError::Scope))?,
            local.binder_info,
        );
    }
    Ok(type_)
}

fn bind(
    context: &mut Context,
    mut term: Typed,
    locals: &[LocalDecl],
) -> Result<Typed, NatDefinitionElabError> {
    term.type_ = forall(context, term.type_, locals)?;
    for local in locals.iter().rev() {
        context.tick()?;
        term.value = Expr::lam(
            local.user_name.clone(),
            context.instantiate(&local.type_)?,
            term.value
                .abstract_fvar(&local.id, 0)
                .map_err(|_| failure(SourceInferenceError::Scope))?,
            local.binder_info,
        );
    }
    context.finish(term)
}

fn class_type(context: &mut Context, carrier: &Expr) -> Result<Typed, NatDefinitionElabError> {
    let carrier = typed(context, carrier.clone())?;
    let class = call(context, "DecidableEq", &[carrier])?;
    context.finish(class)
}

fn equation(
    context: &mut Context,
    left: Typed,
    right: Typed,
) -> Result<Typed, NatDefinitionElabError> {
    let carrier = typed(context, left.type_.clone())?;
    call(context, "Eq", &[carrier, left, right])
}

fn reflexivity(context: &mut Context, term: Typed) -> Result<Typed, NatDefinitionElabError> {
    let carrier = typed(context, term.type_.clone())?;
    call(context, "Eq.refl", &[carrier, term])
}

fn decision_type(
    context: &mut Context,
    proposition: Typed,
) -> Result<Typed, NatDefinitionElabError> {
    call(context, "Decidable", &[proposition])
}

fn proof_field(context: &mut Context, field: &LocalDecl) -> Result<bool, NatDefinitionElabError> {
    let sort = context
        .known_type(&field.type_)?
        .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
    Ok(matches!(context.whnf(&sort)?.node(), ExprNode::Sort { level } if level.is_zero()))
}

struct Family<'a> {
    family: &'a InductiveVal,
    metadata: RecursorVal,
    parameters: &'a [LocalDecl],
    target: &'a Expr,
    levels: Vec<Level>,
}

struct Minor {
    constructor: ConstructorVal,
    major: Typed,
    fields: Vec<LocalDecl>,
    hypotheses: Vec<Option<LocalDecl>>,
    locals: Vec<LocalDecl>,
    result: Expr,
}

fn constructor(
    context: &mut Context,
    family: &Family<'_>,
    name: &Name,
    fields: u32,
) -> Result<ConstructorVal, NatDefinitionElabError> {
    let Some(ConstantInfo::Ctor(constructor)) = context.txn.env.find(name).cloned() else {
        return Err(unsupported(&family.family.base.name));
    };
    if constructor.is_unsafe
        || constructor.induct != family.family.base.name
        || constructor.num_params != family.family.num_params
        || constructor.num_fields != fields
        || !family.family.ctors.contains(name)
    {
        return Err(unsupported(&family.family.base.name));
    }
    if constructor.num_fields as usize > crate::records::RecordBudget::default().max_binders {
        return Err(failure(SourceInferenceError::ResourceLimit));
    }
    Ok(constructor)
}

fn constructor_prefix(
    context: &mut Context,
    family: &Family<'_>,
    constructor: &ConstructorVal,
) -> Result<Typed, NatDefinitionElabError> {
    let mut term = typed(
        context,
        Expr::const_(constructor.base.name.clone(), family.levels.clone()),
    )?;
    for parameter in family.parameters {
        term = context.match_apply(term, value(parameter))?;
    }
    Ok(term)
}

fn open_minor(
    context: &mut Context,
    family: &Family<'_>,
    function: &Typed,
    constructor: ConstructorVal,
) -> Result<Minor, NatDefinitionElabError> {
    let type_ = context.whnf(&function.type_)?;
    let ExprNode::ForallE { binder_type, .. } = type_.node() else {
        return Err(unsupported(&family.family.base.name));
    };
    let mut result = binder_type.clone();
    let recursive = context.constructor_recursive_fields(&constructor)?;
    let mut fields = Vec::new();
    let mut major = constructor_prefix(context, family, &constructor)?;
    for recursive in &recursive {
        let field = open_binder(context, &mut result)?;
        if *recursive {
            // An immediate child has this very family type. A positive
            // function-valued child cannot be decided by a guessed instance.
            context.constrain_type(&field.type_, family.target)?;
        }
        major = context.match_apply(major, value(&field))?;
        fields.push(field);
    }
    let mut locals = fields.clone();
    let mut hypotheses = Vec::new();
    for recursive in recursive {
        if recursive {
            let hypothesis = open_binder(context, &mut result)?;
            locals.push(hypothesis.clone());
            hypotheses.push(Some(hypothesis));
        } else {
            hypotheses.push(None);
        }
    }
    Ok(Minor {
        constructor,
        major,
        fields,
        hypotheses,
        locals,
        result,
    })
}

fn recursor(
    context: &mut Context,
    family: &Family<'_>,
    motive: Typed,
) -> Result<Typed, NatDefinitionElabError> {
    let mut function = context.constant(&family.metadata.base.name)?;
    for parameter in family.parameters {
        function = context.match_apply(function, value(parameter))?;
    }
    context.match_apply(function, motive)
}

/// `(remaining fields) -> Decidable (left = rightConstructor fields)`. Opening
/// the real constructor telescope retains every dependency on earlier fields.
fn remaining_result(
    context: &mut Context,
    left: &Minor,
    mut right: Typed,
    count: usize,
) -> Result<Expr, NatDefinitionElabError> {
    let saved = context.txn.lctx.clone();
    let mut locals = Vec::new();
    for _ in 0..count {
        let mut cursor = right.type_.clone();
        let field = open_binder(context, &mut cursor)?;
        right = context.match_apply(right, value(&field))?;
        locals.push(field);
    }
    let proposition = equation(context, left.major.clone(), right)?;
    let result = decision_type(context, proposition)?;
    let result = forall(context, result.value, &locals)?;
    context.txn.lctx = saved;
    Ok(result)
}

fn negative_fields(
    context: &mut Context,
    family: &Family<'_>,
    left: &Minor,
    index: usize,
    mut right: Typed,
    negative: &LocalDecl,
) -> Result<Typed, NatDefinitionElabError> {
    let saved = context.txn.lctx.clone();
    let mut locals = Vec::new();
    for _ in index + 1..left.fields.len() {
        let mut cursor = right.type_.clone();
        let field = open_binder(context, &mut cursor)?;
        right = context.match_apply(right, value(&field))?;
        locals.push(field);
    }
    let proposition = equation(context, left.major.clone(), right)?;
    let equality = local(
        context,
        named("h"),
        proposition.value.clone(),
        BinderInfo::Default,
    )?;
    let injected = context
        .constructor_injection_evidence(&value(&equality), index)?
        .ok_or_else(|| unsupported(&family.family.base.name))?;
    let contradiction = context.match_apply(value(negative), injected)?;
    let no_equality = bind(context, contradiction, &[equality])?;
    let result = call(context, "Decidable.isFalse", &[proposition, no_equality])?;
    let result = bind(context, result, &locals)?;
    context.txn.lctx = saved;
    Ok(result)
}

/// Rewrite the remaining function's *whole type*, not its free variables in a
/// live context. The actual field-equality witness stays in the Eq.rec term.
fn transport_remaining(
    context: &mut Context,
    left: &LocalDecl,
    right: &LocalDecl,
    evidence: Typed,
    base: Typed,
    result_type: &Expr,
) -> Result<Typed, NatDefinitionElabError> {
    let saved = context.txn.lctx.clone();
    let carrier = typed(context, left.type_.clone())?;
    let proposition = equation(context, value(left), value(right))?;
    let witness = local(context, named("h"), proposition.value, BinderInfo::Default)?;
    let result = typed(context, result_type.clone())?;
    let motive = bind(context, result, &[right.clone(), witness])?;
    context.txn.lctx = saved;
    call(
        context,
        "Eq.rec",
        &[carrier, value(left), motive, base, value(right), evidence],
    )
}

/// Construct a function of the remaining right fields. The successful branch
/// is built at the left field and then transported to the actual right field,
/// so dependent proof/field types never receive an unchecked substitution.
fn field_telescope(
    context: &mut Context,
    family: &Family<'_>,
    left: &Minor,
    index: usize,
    right: Typed,
) -> Result<Typed, NatDefinitionElabError> {
    context.tick()?;
    if index == left.fields.len() {
        let proposition = equation(context, left.major.clone(), right)?;
        let proof = reflexivity(context, left.major.clone())?;
        return call(context, "Decidable.isTrue", &[proposition, proof]);
    }
    let saved = context.txn.lctx.clone();
    let mut cursor = right.type_.clone();
    let other = open_binder(context, &mut cursor)?;
    let field = &left.fields[index];
    context.constrain_type(&field.type_, &other.type_)?;
    let with_other = context.match_apply(right.clone(), value(&other))?;
    let result_type = remaining_result(
        context,
        left,
        with_other.clone(),
        left.fields.len() - index - 1,
    )?;
    let with_same = context.match_apply(right, value(field))?;
    let base = field_telescope(context, family, left, index + 1, with_same)?;
    let proposition = equation(context, value(field), value(&other))?;
    let result = if proof_field(context, field)? {
        let evidence = reflexivity(context, value(field))?;
        transport_remaining(context, field, &other, evidence, base, &result_type)?
    } else {
        let decision = decision_type(context, proposition.clone())?;
        let dictionary = if let Some(hypothesis) = &left.hypotheses[index] {
            context.match_apply(value(hypothesis), value(&other))?
        } else {
            let dictionary = context.instance_hole(decision.value.clone())?;
            context.resolve_instances(true)?;
            Typed {
                value: context.instantiate(&dictionary)?,
                type_: decision.value.clone(),
            }
        };
        context.constrain_type(&dictionary.type_, &decision.value)?;
        let branch_scope = context.txn.lctx.clone();
        let no_type = Expr::forall_e(
            Name::anonymous(),
            proposition.value.clone(),
            Expr::const_(named("False"), Vec::new()),
            BinderInfo::Default,
        );
        let negative = local(context, named("no"), no_type, BinderInfo::Default)?;
        let no = negative_fields(context, family, left, index, with_other, &negative)?;
        let no = bind(context, no, &[negative])?;
        context.txn.lctx = branch_scope.clone();
        let positive = local(
            context,
            named("yes"),
            proposition.value.clone(),
            BinderInfo::Default,
        )?;
        let yes =
            transport_remaining(context, field, &other, value(&positive), base, &result_type)?;
        let yes = bind(context, yes, &[positive])?;
        context.txn.lctx = branch_scope;
        let motive = typed(
            context,
            Expr::lam(
                Name::anonymous(),
                decision.value,
                result_type.clone(),
                BinderInfo::Default,
            ),
        )?;
        call(
            context,
            "Decidable.rec",
            &[proposition, motive, no, yes, dictionary],
        )?
    };
    context.constrain_type(&result.type_, &result_type)?;
    let result = bind(context, result, &[other])?;
    context.txn.lctx = saved;
    Ok(result)
}

fn different_constructors(
    context: &mut Context,
    family: &Family<'_>,
    left: &Minor,
    right: &Minor,
) -> Result<Typed, NatDefinitionElabError> {
    let saved = context.txn.lctx.clone();
    let proposition = equation(context, left.major.clone(), right.major.clone())?;
    let equality = local(
        context,
        named("h"),
        proposition.value.clone(),
        BinderInfo::Default,
    )?;
    let contradiction = context
        .constructor_clash_evidence(&value(&equality))?
        .ok_or_else(|| unsupported(&family.family.base.name))?;
    let no_equality = bind(context, contradiction, &[equality])?;
    let result = call(context, "Decidable.isFalse", &[proposition, no_equality])?;
    context.txn.lctx = saved;
    Ok(result)
}

fn compare_constructor(
    context: &mut Context,
    family: &Family<'_>,
    left: &Minor,
    receiver: &LocalDecl,
) -> Result<Typed, NatDefinitionElabError> {
    let proposition = equation(context, left.major.clone(), value(receiver))?;
    let decision = decision_type(context, proposition)?;
    let motive = bind(context, decision, std::slice::from_ref(receiver))?;
    let mut function = recursor(context, family, motive)?;
    for rule in &family.metadata.rules {
        context.tick()?;
        let saved = context.txn.lctx.clone();
        let constructor = constructor(context, family, &rule.ctor, rule.nfields)?;
        let right = open_minor(context, family, &function, constructor)?;
        let result = if left.constructor.base.name == right.constructor.base.name {
            let prefix = constructor_prefix(context, family, &right.constructor)?;
            let mut comparison = field_telescope(context, family, left, 0, prefix)?;
            for field in &right.fields {
                comparison = context.match_apply(comparison, value(field))?;
            }
            comparison
        } else {
            different_constructors(context, family, left, &right)?
        };
        context.constrain_type(&result.type_, &right.result)?;
        let result = bind(context, result, &right.locals)?;
        function = context.match_apply(function, result)?;
        context.txn.lctx = saved;
    }
    context.match_apply(function, value(receiver))
}

pub(super) fn elaborate(
    context: &mut Context,
    info: &InductiveVal,
    parameters: &[LocalDecl],
    target: &Expr,
) -> Result<DerivedInstance, NatDefinitionElabError> {
    if info.all.len() != 1 || info.num_nested != 0 {
        return Err(unsupported(&info.base.name));
    }
    let target_type = context
        .known_type(target)?
        .ok_or_else(|| unsupported(&info.base.name))?;
    if matches!(context.whnf(&target_type)?.node(), ExprNode::Sort { level } if level.is_zero()) {
        return Err(unsupported(&info.base.name));
    }
    let recursor_name = Name::str(info.base.name.clone(), "rec");
    let Some(ConstantInfo::Rec(metadata)) = context.txn.env.find(&recursor_name).cloned() else {
        return Err(unsupported(&info.base.name));
    };
    if metadata.is_unsafe
        || metadata.num_motives != 1
        || metadata.num_indices != 0
        || metadata.num_params != info.num_params
        || metadata.num_minors as usize != info.ctors.len()
        || metadata.rules.len() != info.ctors.len()
        || metadata.all != info.all
    {
        return Err(unsupported(&info.base.name));
    }
    let class = class_type(context, target)?;
    let instance = context.generated_instance_name(parameters, &class.value)?;
    let helper = Name::str(instance.clone(), "decEq");
    let family = Family {
        family: info,
        metadata,
        parameters,
        target,
        levels: info
            .base
            .level_params
            .iter()
            .cloned()
            .map(Level::param)
            .collect(),
    };
    let mut header = parameters.to_vec();
    // Match the pin's generic deriving header: every well-typed parameter
    // dictionary follows the complete implicit family-parameter telescope.
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
    let proposition = equation(context, value(&left), value(&right))?;
    let decision = decision_type(context, proposition)?;
    let comparison_type = forall(context, decision.value, std::slice::from_ref(&right))?;
    let motive_type = typed(context, comparison_type)?;
    let motive = bind(context, motive_type, std::slice::from_ref(&left))?;
    let mut function = recursor(context, &family, motive)?;
    for rule in &family.metadata.rules {
        context.tick()?;
        let saved = context.txn.lctx.clone();
        let constructor = constructor(context, &family, &rule.ctor, rule.nfields)?;
        let mut branch = open_minor(context, &family, &function, constructor)?;
        let receiver = open_binder(context, &mut branch.result)?;
        let result = compare_constructor(context, &family, &branch, &receiver)?;
        context.constrain_type(&result.type_, &branch.result)?;
        branch.locals.push(receiver);
        let result = bind(context, result, &branch.locals)?;
        function = context.match_apply(function, result)?;
        context.txn.lctx = saved;
    }
    let result = context.match_apply(function, value(&left))?;
    let result = context.match_apply(result, value(&right))?;
    let mut helper_header = header.clone();
    helper_header.extend([left, right]);
    let helper_term = close(context, result, &helper_header)?;
    let mut helper_call = Typed {
        value: Expr::const_(helper.clone(), family.levels),
        type_: helper_term.type_.clone(),
    };
    for parameter in &header {
        helper_call = context.match_apply(helper_call, value(parameter))?;
    }
    context.constrain_type(&helper_call.type_, &class.value)?;
    let instance_term = close(
        context,
        Typed {
            value: helper_call.value,
            type_: class.value,
        },
        &header,
    )?;
    let definition = |name: Name, term: Typed| {
        Declaration::Defn(DefinitionVal {
            base: ConstantVal {
                name: name.clone(),
                level_params: info.base.level_params.clone(),
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
