//! Registration-time native index models, independent of later attributes.
//!
//! Tags 4/5/6 extend the ordinary strict/global/scoped journal operations with
//! an explicit optional model. Absence of this trailer (the legacy tags) is
//! different from a captured unsupported model: the latter must never acquire
//! a different path merely because a later declaration or attribute changed.
use super::*;

#[cfg(test)]
mod tests;

pub(super) fn read(
    bytes: &mut &[u8],
) -> Result<Option<export::DerivedIndex>, InstanceRegistryError> {
    match take(bytes, 1)?[0] {
        0 => Ok(None),
        1 => {
            let keys = discr_tree::read_keys(bytes)?;
            let count = u32::from_le_bytes(
                take(bytes, 4)?
                    .try_into()
                    .map_err(|_| InstanceRegistryError::Malformed)?,
            );
            let size = usize::try_from(count)
                .ok()
                .and_then(|count| count.checked_mul(4))
                .ok_or(InstanceRegistryError::Limit)?;
            if size > MAX_ENTRY_BYTES {
                return Err(InstanceRegistryError::Limit);
            }
            // Prove all encoded storage exists before allocating from a count.
            let encoded = take(bytes, size)?;
            let mut synth_order = Vec::with_capacity(encoded.len() / 4);
            let mut seen = BTreeSet::new();
            for chunk in encoded.as_chunks::<4>().0 {
                let position = u32::from_le_bytes(*chunk);
                if !seen.insert(position) {
                    return Err(InstanceRegistryError::Malformed);
                }
                synth_order.push(position);
            }
            Ok(Some(export::DerivedIndex { keys, synth_order }))
        }
        _ => Err(InstanceRegistryError::Malformed),
    }
}

/// Validate the immutable declaration facts and path grammar, without deriving
/// a new model under the current reducibility or class-registration epoch.
pub(super) fn validate(
    env: &Environment,
    class: &Name,
    declaration: &Name,
    model: Option<&export::DerivedIndex>,
) -> Result<(), InstanceRegistryError> {
    validate_with_budget(env, class, declaration, model, &mut 1_000_000)
}

pub(super) fn validate_with_budget(
    env: &Environment,
    class: &Name,
    declaration: &Name,
    model: Option<&export::DerivedIndex>,
    remaining: &mut usize,
) -> Result<(), InstanceRegistryError> {
    let Some(model) = model else {
        return Ok(());
    };
    spend(remaining)?;
    let class_info = env.find(class).ok_or(InstanceRegistryError::Malformed)?;
    let mut class_type = &class_info.constant_val().type_;
    let mut arity = 0u32;
    loop {
        spend(remaining)?;
        match class_type.node() {
            ExprNode::ForallE { body, .. } => {
                arity = arity.checked_add(1).ok_or(InstanceRegistryError::Limit)?;
                class_type = body;
            }
            ExprNode::MData { expr, .. } => class_type = expr,
            ExprNode::Sort { .. } => break,
            _ => return Err(InstanceRegistryError::Malformed),
        }
    }
    if !matches!(model.keys.first(), Some(discr_tree::Key::Const(name, count))
        if name == class && *count == arity)
    {
        return Err(InstanceRegistryError::Malformed);
    }
    let mut pending = 1usize;
    for key in &model.keys {
        spend(remaining)?;
        pending = pending
            .checked_sub(1)
            .and_then(|pending| pending.checked_add(key.arity()))
            .ok_or(InstanceRegistryError::Malformed)?;
        match key {
            discr_tree::Key::Const(name, _) if env.contains(name) => {}
            discr_tree::Key::Star
            | discr_tree::Key::Other
            | discr_tree::Key::Lit(_)
            | discr_tree::Key::Arrow => {}
            // Native derivation does not emit open or projection paths. Their
            // imported representation remains governed by the foreign reader.
            _ => return Err(InstanceRegistryError::Malformed),
        }
    }
    if pending != 0 {
        return Err(InstanceRegistryError::Malformed);
    }
    let info = env
        .find(declaration)
        .ok_or(InstanceRegistryError::Malformed)?;
    let (binders, observed_class) =
        immutable_telescope(env, &info.constant_val().type_, remaining)?;
    let mut expected = BTreeSet::new();
    for (index, binder) in binders.iter().enumerate() {
        spend(remaining)?;
        if *binder == BinderInfo::InstImplicit {
            expected.insert(u32::try_from(index).map_err(|_| InstanceRegistryError::Limit)?);
        }
    }
    let mut actual = BTreeSet::new();
    for index in &model.synth_order {
        spend(remaining)?;
        actual.insert(*index);
    }
    if observed_class != *class || actual.len() != model.synth_order.len() || actual != expected {
        return Err(InstanceRegistryError::Malformed);
    }
    Ok(())
}

fn spend(remaining: &mut usize) -> Result<(), InstanceRegistryError> {
    *remaining = remaining
        .checked_sub(1)
        .ok_or(InstanceRegistryError::Limit)?;
    Ok(())
}

/// The same attribute-independent telescope as `instance_telescope`, with
/// caller work charged before binder allocation and capture-preserving beta.
fn immutable_telescope(
    env: &Environment,
    type_: &Expr,
    remaining: &mut usize,
) -> Result<(Vec<BinderInfo>, Name), InstanceRegistryError> {
    let mut current = type_.clone();
    let mut binders = Vec::new();
    loop {
        spend(remaining)?;
        match current.node() {
            ExprNode::ForallE {
                binder_info, body, ..
            } => {
                binders.push(*binder_info);
                current = body.clone();
            }
            ExprNode::MData { expr, .. } => current = expr.clone(),
            _ => {
                let mut head = &current;
                let mut args = Vec::new();
                while let ExprNode::App { f, a } = head.node() {
                    spend(remaining)?;
                    args.push(a.clone());
                    head = f;
                }
                args.reverse();
                let function = match head.node() {
                    ExprNode::Const { name, levels } => match env.find(name) {
                        Some(ConstantInfo::Defn(value))
                            if value.safety == DefinitionSafety::Safe
                                && value.hints == ReducibilityHints::Abbrev
                                && value.base.level_params.len() == levels.len() =>
                        {
                            &value.value
                        }
                        _ => return Ok((binders, name.clone())),
                    },
                    ExprNode::Lam { .. } if !args.is_empty() => head,
                    _ => return Err(InstanceRegistryError::Malformed),
                };
                let mut todo = vec![function];
                todo.extend(args.iter());
                let mut seen = std::collections::HashSet::new();
                while let Some(expr) = todo.pop() {
                    spend(remaining)?;
                    if !seen.insert(expr.allocation_identity()) {
                        continue;
                    }
                    match expr.node() {
                        ExprNode::App { f, a } => todo.extend([f, a]),
                        ExprNode::ForallE {
                            binder_type, body, ..
                        }
                        | ExprNode::Lam {
                            binder_type, body, ..
                        } => todo.extend([binder_type, body]),
                        ExprNode::LetE {
                            type_, value, body, ..
                        } => todo.extend([type_, value, body]),
                        ExprNode::Proj { expr, .. } | ExprNode::MData { expr, .. } => {
                            todo.push(expr)
                        }
                        _ => {}
                    }
                }
                current = beta(function, &args).ok_or(InstanceRegistryError::Malformed)?;
            }
        }
    }
}

/// Compute once at a validated registration snapshot. A new priority cannot
/// silently move a declaration between tree leaves or prerequisite schedules.
pub(super) fn derive(
    env: &Environment,
    registry: &InstanceRegistry,
    declaration: &Name,
) -> Result<Option<export::DerivedIndex>, InstanceRegistryError> {
    let model = export::derive_registration_index(env, registry, declaration, &mut 1_000_000)?;
    let same = if let Some(previous) = registry.imported.instances.get(declaration) {
        model.as_ref().is_some_and(|model| {
            model.keys == previous.keys && model.synth_order == previous.synth_order
        })
    } else if let Some(previous) = registry.captured_instance_index(declaration) {
        matches!((previous, model.as_ref()), (Some(previous), Some(model)) if previous == model)
    } else if registry.updates.contains_key(declaration) {
        // Legacy rows have no snapshot. Only their conservative, immutable
        // model can justify an update to a newly captured native registration.
        let previous = export::derive_index(env, registry, declaration, &mut 1_000_000)?;
        matches!((&previous, &model), (Some(previous), Some(model)) if previous == model)
    } else {
        true
    };
    if !same {
        return Err(InstanceRegistryError::UnsupportedIndexUpdate(
            declaration.clone(),
        ));
    }
    Ok(model)
}

pub(super) fn payload(
    operation: u8,
    class: &Name,
    declaration: &Name,
    priority: u32,
    scope: Option<&Name>,
    model: Option<&export::DerivedIndex>,
) -> Result<Vec<u8>, InstanceRegistryError> {
    if !(1..=3).contains(&operation) || (operation == 3) != scope.is_some() {
        return Err(InstanceRegistryError::Malformed);
    }
    let mut payload = instance_payload(operation + 3, class, declaration, priority, scope)?;
    match model {
        None => payload.push(0),
        Some(model) => {
            payload.push(1);
            discr_tree::write_keys(&model.keys, &mut payload)?;
            let added = model
                .synth_order
                .len()
                .checked_add(1)
                .and_then(|count| count.checked_mul(4))
                .ok_or(InstanceRegistryError::Limit)?;
            if payload.len().saturating_add(added) > MAX_ENTRY_BYTES {
                return Err(InstanceRegistryError::Limit);
            }
            payload.extend(
                u32::try_from(model.synth_order.len())
                    .map_err(|_| InstanceRegistryError::Limit)?
                    .to_le_bytes(),
            );
            for index in &model.synth_order {
                payload.extend(index.to_le_bytes());
            }
        }
    }
    if payload.len() > MAX_ENTRY_BYTES {
        return Err(InstanceRegistryError::Limit);
    }
    Ok(payload)
}
