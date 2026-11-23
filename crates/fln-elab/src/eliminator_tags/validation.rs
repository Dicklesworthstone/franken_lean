//! Bounded `getElabElimInfo` header validation, not a type checker. The
//! declaration and every dependency must already be admitted. Registration
//! proves only that the supported dependent-application path can interpret
//! the telescope; the ordinary elaborator and checkers validate each use.
use super::*;
use fln_core::expr::{BinderInfo, ExprNode};
use fln_env::constants::{DefinitionSafety, ReducibilityHints};

type Binder = (Name, Expr, BinderInfo);

fn spend(remaining: &mut usize) -> Result<(), EliminatorTagError> {
    *remaining = remaining.checked_sub(1).ok_or(EliminatorTagError::Limit)?;
    Ok(())
}

fn scan(root: &Expr, remaining: &mut usize) -> Result<(), EliminatorTagError> {
    let mut pending = vec![root];
    let mut seen = std::collections::HashSet::new();
    while let Some(expr) = pending.pop() {
        spend(remaining)?;
        if !seen.insert(expr.allocation_identity()) {
            continue;
        }
        match expr.node() {
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
    Ok(())
}

/// Default-transparency beta/zeta/delta steps needed to expose telescope
/// binders. Recursor, quotient, projection and smart reductions have explicit
/// unsupported outcomes rather than an inferred binder shape.
fn header_whnf(
    env: &Environment,
    declaration: &Name,
    expression: &Expr,
    remaining: &mut usize,
) -> Result<Expr, EliminatorTagError> {
    let mut head = expression.clone();
    let mut arguments = Vec::new();
    loop {
        spend(remaining)?;
        match head.node() {
            ExprNode::App { f, a } => {
                arguments.push(a.clone());
                head = f.clone();
            }
            ExprNode::MData { expr, .. } => head = expr.clone(),
            ExprNode::LetE { body, value, .. } => {
                scan(body, remaining)?;
                head = body
                    .subst_loose(0, std::slice::from_ref(value))
                    .map_err(|_| EliminatorTagError::Limit)?;
            }
            ExprNode::Lam { body, .. } if !arguments.is_empty() => {
                scan(body, remaining)?;
                let argument = arguments.pop().ok_or(EliminatorTagError::Malformed)?;
                head = body
                    .subst_loose(0, &[argument])
                    .map_err(|_| EliminatorTagError::Limit)?;
            }
            ExprNode::Proj { .. } => {
                return Err(EliminatorTagError::UnsupportedEliminator(
                    declaration.clone(),
                ));
            }
            ExprNode::Const { name, levels } => {
                let info = env
                    .find(name)
                    .ok_or_else(|| EliminatorTagError::UnknownDeclaration(name.clone()))?;
                match info {
                    ConstantInfo::Rec(_)
                    | ConstantInfo::Quot(_)
                    | ConstantInfo::Opaque(_)
                    | ConstantInfo::Axiom(_) => {
                        // Public unexposed definitions are retained as axiom
                        // interfaces. Their hidden bodies cannot be used here
                        // to reconstruct a telescope from complete metadata.
                        return Err(EliminatorTagError::UnsupportedEliminator(
                            declaration.clone(),
                        ));
                    }
                    ConstantInfo::Defn(definition) => {
                        let status = crate::reducibility::table(env)
                            .map_err(|error| match error {
                                crate::reducibility::ReducibilityError::Limit
                                | crate::reducibility::ReducibilityError::Instances(
                                    InstanceRegistryError::Limit,
                                ) => EliminatorTagError::Limit,
                                _ => EliminatorTagError::Malformed,
                            })?
                            .get(name);
                        if status == Some(crate::reducibility::Reducibility::Irreducible)
                            || (status.is_none() && definition.hints == ReducibilityHints::Opaque)
                            || definition.safety != DefinitionSafety::Safe
                            || env.contains(&Name::str(name.clone(), "_sunfold"))
                        {
                            // A valid imported tag may predate a later opacity
                            // policy. Current failure to expose its telescope
                            // is a coverage boundary, not evidence of forgery.
                            return Err(EliminatorTagError::UnsupportedEliminator(
                                declaration.clone(),
                            ));
                        }
                        if !arguments.is_empty()
                            && let Some(projection) = crate::records::projection::class_projection(
                                env,
                                definition,
                                || spend(remaining),
                            )?
                            && crate::instances::InstanceRegistry::read(env)
                                .map_err(codec)?
                                .is_class(&projection.structure)
                        {
                            return Err(EliminatorTagError::UnsupportedEliminator(
                                declaration.clone(),
                            ));
                        }
                        head = crate::universe::parameters::instantiate(
                            || spend(remaining),
                            || EliminatorTagError::Malformed,
                            &definition.value,
                            &definition.base.level_params,
                            levels,
                        )?;
                    }
                    _ => break,
                }
            }
            _ => break,
        }
    }
    for argument in arguments.into_iter().rev() {
        spend(remaining)?;
        head = Expr::app(head, argument);
    }
    Ok(head)
}

/// `forallTelescopeReducing` defaults `whnfType` to false. Keep the original
/// final expression unless its WHNF actually exposes another forall binder.
fn telescope(
    env: &Environment,
    declaration: &Name,
    type_: &Expr,
    remaining: &mut usize,
) -> Result<(Vec<Binder>, Expr), EliminatorTagError> {
    let mut binders = Vec::new();
    let mut current = type_.clone();
    loop {
        spend(remaining)?;
        if !matches!(current.node(), ExprNode::ForallE { .. }) {
            let reduced = header_whnf(env, declaration, &current, remaining)?;
            if matches!(reduced.node(), ExprNode::ForallE { .. }) {
                current = reduced;
            } else {
                return Ok((binders, current));
            }
        }
        let ExprNode::ForallE {
            binder_name,
            binder_type,
            body,
            binder_info,
        } = current.node()
        else {
            unreachable!("telescope continuation has a forall");
        };
        binders.push((binder_name.clone(), binder_type.clone(), *binder_info));
        current = body.clone();
    }
}

fn app_head_arity<'a>(
    expr: &'a Expr,
    remaining: &mut usize,
) -> Result<(&'a Expr, usize), EliminatorTagError> {
    let mut head = expr;
    let mut arity = 0usize;
    while let ExprNode::App { f, .. } = head.node() {
        spend(remaining)?;
        head = f;
        arity = arity.checked_add(1).ok_or(EliminatorTagError::Limit)?;
    }
    Ok((head, arity))
}

fn close(binders: Vec<Binder>, mut result: Expr) -> Expr {
    for (name, domain, style) in binders.into_iter().rev() {
        result = Expr::forall_e(name, domain, result, style);
    }
    result
}

pub(super) fn eliminator_type(
    env: &Environment,
    info: &ConstantInfo,
    remaining: &mut usize,
) -> Result<Expr, EliminatorTagError> {
    let name = info.name();
    let invalid = || EliminatorTagError::InvalidEliminator(name.clone());
    scan(&info.constant_val().type_, remaining)?;
    let (mut binders, result) = telescope(env, name, &info.constant_val().type_, remaining)?;
    // `hasOptAutoParams` inspects each original binder domain syntactically.
    for (_, domain, _) in &binders {
        let (head, arity) = app_head_arity(domain, remaining)?;
        if arity == 2
            && matches!(head.node(), ExprNode::Const { name, .. }
                if name == &Name::from_components(["optParam"])
                    || name == &Name::from_components(["autoParam"]))
        {
            return Err(invalid());
        }
    }
    let (head, arity) = app_head_arity(&result, remaining)?;
    let ExprNode::BVar { idx } = head.node() else {
        return Err(invalid());
    };
    if arity == 0 || *idx as usize >= binders.len() {
        return Err(invalid());
    }
    let motive_pos = binders.len() - 1 - *idx as usize;
    let (motive_binders, motive_result) = telescope(env, name, &binders[motive_pos].1, remaining)?;
    if motive_binders.len() != arity || !matches!(motive_result.node(), ExprNode::Sort { .. }) {
        return Err(invalid());
    }
    binders[motive_pos].1 = close(motive_binders, motive_result);
    Ok(close(binders, result))
}
