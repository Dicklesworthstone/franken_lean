//! Native construction of the pin's derived Nonempty proof.
//!
//! The handler in Lean/Elab/Deriving/Nonempty.lean tries constructors in order,
//! using the admitted Classical.ofNonempty for the remaining field goals. Its
//! generated `variable` binders retain only the Nonempty assumptions actually
//! used by the successful proof, interleaved with the family arguments.
use super::*;
use fln_core::level::LevelView;
use fln_env::constants::{ConstructorVal, TheoremVal};

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

fn class_type(context: &mut Context, carrier: &Expr) -> Result<Typed, NatDefinitionElabError> {
    let carrier = typed(context, carrier.clone())?;
    call(context, "Nonempty", &[carrier])
}

fn private_name(context: &mut Context, name: &Name) -> Result<bool, NatDefinitionElabError> {
    let mut prefix = name.clone();
    while !prefix.is_anonymous() {
        context.tick()?;
        if prefix == named("_private") {
            return Ok(true);
        }
        prefix = prefix.parent();
    }
    Ok(false)
}

/// `withoutExposeFromCtors` inspects every member of a mutual family. A
/// requested expose attribute on a public type with any private constructor is
/// an error even though the derived instance is a theorem with a hidden proof.
fn check_exposure(
    context: &mut Context,
    family: &InductiveVal,
) -> Result<(), NatDefinitionElabError> {
    if !context.source_scope.expose_definitions || private_name(context, &family.base.name)? {
        return Ok(());
    }
    for name in &family.all {
        context.tick()?;
        let Some(ConstantInfo::Induct(member)) = context.txn.env.find(name).cloned() else {
            return Err(unsupported(&family.base.name));
        };
        for constructor in &member.ctors {
            if private_name(context, constructor)? {
                return Err(NatDefinitionElabError::UnexpectedSyntax {
                    expected: "Nonempty deriving without expose for a public type with private constructors",
                });
            }
        }
    }
    Ok(())
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

/// `Meta.decLevel?` on the closed levels in an admitted family telescope.
/// An arbitrary Sort parameter is not known to be a Type. Both operands of
/// max/imax must admit a predecessor, as in the pin's DecLevel.decAux?.
fn type_level(context: &mut Context, level: &Level) -> Result<bool, NatDefinitionElabError> {
    let mut pending = vec![level];
    while let Some(level) = pending.pop() {
        context.tick()?;
        match level.view() {
            LevelView::Succ(_) => {}
            LevelView::Max(left, right) | LevelView::IMax(left, right) => {
                pending.extend([left, right]);
            }
            LevelView::Zero | LevelView::Param(_) | LevelView::MVar(_) => return Ok(false),
        }
    }
    Ok(true)
}

fn arguments(
    context: &mut Context,
    family: &InductiveVal,
    parameters: &[LocalDecl],
    target: &Expr,
) -> Result<(Vec<LocalDecl>, Expr), NatDefinitionElabError> {
    let mut arguments = parameters.to_vec();
    let mut target = typed(context, target.clone())?;
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
        let argument = local(
            context,
            binder_name.clone(),
            binder_type.clone(),
            BinderInfo::Implicit,
        )?;
        target = context.match_apply(target, value(&argument))?;
        arguments.push(argument);
    }
    Ok((arguments, target.value))
}

struct Header {
    binders: Vec<LocalDecl>,
    assumptions: std::collections::HashSet<FVarId>,
}

fn header(
    context: &mut Context,
    arguments: &[LocalDecl],
) -> Result<Header, NatDefinitionElabError> {
    let mut binders = Vec::new();
    let mut assumptions = std::collections::HashSet::new();
    // The generated `{arg}` variables initially have unknown types. Unlike a
    // written `{arg : Class ...}`, inferring that type from the target later
    // does not register an original argument as a local instance. Fresh
    // `[Nonempty arg]` binders are typed at introduction and remain eligible.
    context
        .excluded_local_instances
        .extend(arguments.iter().map(|argument| argument.id.clone()));
    for (index, argument) in arguments.iter().enumerate() {
        context.tick()?;
        binders.push(argument.clone());
        let domain = context.whnf(&argument.type_)?;
        let ExprNode::Sort { level } = domain.node() else {
            continue;
        };
        if !type_level(context, level)? {
            continue;
        }
        let class = class_type(context, &Expr::fvar(argument.id.clone()))?;
        let class = context.finish(class)?;
        let hypothesis = local(
            context,
            named(&format!("inst{index}")),
            class.value,
            BinderInfo::InstImplicit,
        )?;
        assumptions.insert(hypothesis.id.clone());
        binders.push(hypothesis);
    }
    Ok(Header {
        binders,
        assumptions,
    })
}

struct Field {
    hole: Expr,
    type_: Expr,
}

fn unassigned(context: &Context, field: &Field) -> Result<bool, NatDefinitionElabError> {
    let ExprNode::MVar { id } = field.hole.node() else {
        return Err(failure(SourceInferenceError::Scope));
    };
    Ok(!context.txn.mvars.is_assigned(id))
}

fn contains_goal(
    context: &mut Context,
    expression: &Expr,
    goal: &MVarId,
) -> Result<bool, NatDefinitionElabError> {
    let mut pending = vec![expression];
    let mut seen = std::collections::HashSet::new();
    while let Some(expression) = pending.pop() {
        context.tick()?;
        if !expression.has_expr_mvar() || !seen.insert(expression.allocation_identity()) {
            continue;
        }
        match expression.node() {
            ExprNode::MVar { id } if id == goal => return Ok(true),
            ExprNode::App { f, a } => pending.extend([f, a]),
            ExprNode::ForallE {
                binder_type, body, ..
            }
            | ExprNode::Lam {
                binder_type, body, ..
            } => pending.extend([binder_type, body]),
            ExprNode::LetE {
                type_, value, body, ..
            } => pending.extend([type_, value, body]),
            ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => pending.push(expr),
            _ => {}
        }
    }
    Ok(false)
}

/// `apply` presents nondependent goals first. Choosing a value for a type or
/// index before the dependent goals would accept programs the pin rejects.
fn goal_order(
    context: &mut Context,
    fields: &[Field],
) -> Result<Vec<usize>, NatDefinitionElabError> {
    let mut pending = Vec::new();
    for (index, field) in fields.iter().enumerate() {
        if unassigned(context, field)? {
            pending.push((index, context.instantiate(&field.type_)?));
        }
    }
    let mut independent = Vec::new();
    let mut dependent = Vec::new();
    for (index, _) in &pending {
        let ExprNode::MVar { id } = fields[*index].hole.node() else {
            return Err(failure(SourceInferenceError::Scope));
        };
        let mut used_by_other = false;
        for (other, type_) in &pending {
            if index != other && contains_goal(context, type_, id)? {
                used_by_other = true;
                break;
            }
        }
        if used_by_other {
            dependent.push(*index);
        } else {
            independent.push(*index);
        }
    }
    independent.extend(dependent);
    Ok(independent)
}

fn of_nonempty(context: &mut Context, type_: &Expr) -> Result<Typed, NatDefinitionElabError> {
    let class = class_type(context, type_)?;
    let dictionary = context.instance_hole(class.value.clone())?;
    context.resolve_instances(true)?;
    let dictionary = Typed {
        value: context.instantiate(&dictionary)?,
        type_: context.instantiate(&class.value)?,
    };
    let carrier = context.instantiate(type_)?;
    let carrier = typed(context, carrier)?;
    call(context, "Classical.ofNonempty", &[carrier, dictionary])
}

fn candidate(
    context: &mut Context,
    family: &InductiveVal,
    constructor: &ConstructorVal,
    parameters: &[LocalDecl],
    target: &Expr,
) -> Result<Typed, NatDefinitionElabError> {
    let levels: Vec<_> = family
        .base
        .level_params
        .iter()
        .cloned()
        .map(Level::param)
        .collect();
    let type_ = context.instantiate_params(
        &constructor.base.type_,
        &constructor.base.level_params,
        &levels,
    )?;
    let parameter_values: Vec<_> = parameters
        .iter()
        .map(|parameter| Expr::fvar(parameter.id.clone()))
        .collect();
    let mut witness = apply(
        context,
        Typed {
            value: Expr::const_(constructor.base.name.clone(), levels),
            type_,
        },
        &parameter_values,
    )?;
    let mut fields = Vec::new();
    for _ in 0..constructor.num_fields {
        context.tick()?;
        let cursor = context.whnf(&witness.type_)?;
        let ExprNode::ForallE {
            binder_type,
            binder_info,
            body,
            ..
        } = cursor.node()
        else {
            return Err(unsupported(&family.base.name));
        };
        // `apply @Ctor` synthesizes instance-implicit arguments before it
        // returns the remaining goals to `exact Classical.ofNonempty`.
        let hole = if *binder_info == BinderInfo::InstImplicit {
            context.instance_hole(binder_type.clone())?
        } else {
            context.hole(binder_type.clone())?
        };
        witness.value = Expr::app(witness.value, hole.clone());
        witness.type_ = context.substitute(body, &hole)?;
        fields.push(Field {
            hole,
            type_: binder_type.clone(),
        });
    }
    context.equations.push(SourceEquation::selection(
        witness.type_.clone(),
        target.clone(),
    ));
    context.flush(true)?;
    context.resolve_instances(true)?;
    for index in goal_order(context, &fields)? {
        let field = &fields[index];
        if !unassigned(context, field)? {
            continue;
        }
        let type_ = context.instantiate(&field.type_)?;
        let chosen = of_nonempty(context, &type_)?;
        context
            .equations
            .push(SourceEquation::inference(field.hole.clone(), chosen.value));
        context.flush(true)?;
    }
    let witness = context.finish(witness)?;
    let carrier = typed(context, target.clone())?;
    let proof = call(context, "Nonempty.intro", &[carrier, witness])?;
    context.finish(proof)
}

pub(super) fn elaborate(
    context: &mut Context,
    family: &InductiveVal,
    parameters: &[LocalDecl],
    target: &Expr,
) -> Result<DerivedInstance, NatDefinitionElabError> {
    check_exposure(context, family)?;
    let (arguments, target) = arguments(context, family, parameters, target)?;
    let class = class_type(context, &target)?;
    let class = context.finish(class)?;
    let instance = context.generated_instance_name(&arguments, &class.value)?;
    let header = header(context, &arguments)?;
    for name in &family.ctors {
        context.tick()?;
        let Some(ConstantInfo::Ctor(constructor)) = context.txn.env.find(name).cloned() else {
            return Err(unsupported(&family.base.name));
        };
        if constructor.is_unsafe
            || constructor.induct != family.base.name
            || constructor.num_params != family.num_params
        {
            return Err(unsupported(&family.base.name));
        }
        if constructor.num_fields as usize > crate::records::RecordBudget::default().max_binders {
            return Err(failure(SourceInferenceError::ResourceLimit));
        }
        let mut trial = context.clone();
        let result = candidate(&mut trial, family, &constructor, parameters, &target);
        // Constructor backtracking never refunds work, cancellation or faults.
        context.txn.budget.heartbeats_consumed = trial.txn.budget.heartbeats_consumed;
        let proof = match result {
            Ok(proof) => proof,
            Err(error) if normal_failure(&error) => continue,
            Err(error) => return Err(error),
        };
        let mut binders = Vec::new();
        for binder in &header.binders {
            trial.tick()?;
            let unused = header.assumptions.contains(&binder.id)
                && proof
                    .value
                    .abstract_fvar(&binder.id, 0)
                    .map_err(|_| failure(SourceInferenceError::Scope))?
                    == proof.value;
            if !unused {
                binders.push(binder.clone());
            }
        }
        let term = close(&mut trial, proof, &binders)?;
        let declaration = Declaration::Thm(TheoremVal {
            base: ConstantVal {
                name: instance.clone(),
                level_params: family.base.level_params.clone(),
                type_: term.type_,
            },
            value: term.value,
            all: vec![instance.clone()],
        });
        *context = trial;
        return Ok(DerivedInstance {
            declarations: vec![declaration],
            instance,
        });
    }
    Err(failure(SourceInferenceError::Deriving(
        DerivingError::CannotDeriveNonempty(family.base.name.clone()),
    )))
}
