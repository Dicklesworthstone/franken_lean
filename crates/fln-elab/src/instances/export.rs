//! Semantic class metadata for source-module export. No declaration authority.
use super::*;
use fln_core::level::LevelView;
use std::collections::HashSet;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ClassRegistration {
    pub name: Name,
    pub parameters: imported::ClassParameters,
}

pub fn supports(descriptor_: &ExtensionDescriptor) -> bool {
    *descriptor_ == descriptor()
}

pub fn journal_name() -> Name {
    extension_name()
}

/// Export only this module's exact new journal suffix. `None` means a journal
/// operation has no faithful serializer yet; it must never be discarded.
pub fn classes(
    base: &Environment,
    result: &Environment,
    max_work: usize,
) -> Result<Option<(Vec<ClassRegistration>, usize)>, InstanceRegistryError> {
    let registry = InstanceRegistry::read(result)?;
    let Some(current) = result.extension(&extension_name()) else {
        if base.extension(&extension_name()).is_some() {
            return Err(InstanceRegistryError::Malformed);
        }
        return Ok(Some((Vec::new(), 0)));
    };
    let prior = base.extension(&extension_name());
    let start = prior.map_or(0, |prior| prior.len());
    if current.descriptor != descriptor() {
        return Err(InstanceRegistryError::Malformed);
    }
    if let Some(prior) = prior
        && (prior.descriptor != current.descriptor
            || prior.len() > current.len()
            || !prior.entries().zip(current.entries()).all(|(a, b)| a == b))
    {
        return Err(InstanceRegistryError::Malformed);
    }
    let mut rows = Vec::new();
    let mut remaining = max_work;
    for entry in current.entries().skip(start) {
        tick(&mut remaining)?;
        let mut bytes: &[u8] = &entry.payload;
        if take(&mut bytes, MAGIC.len())? != MAGIC {
            return Err(InstanceRegistryError::Malformed);
        }
        if take(&mut bytes, 1)?[0] != 0 {
            return Ok(None);
        }
        let name = read_name(&mut bytes)?;
        if !bytes.is_empty() {
            return Err(InstanceRegistryError::Malformed);
        }
        let parameters = match registry.imported_class_parameters(&name) {
            Some(parameters) => parameters.clone(),
            None => parameters_with_budget(result, &name, &mut remaining)?,
        };
        rows.push(ClassRegistration { name, parameters });
    }
    Ok(Some((rows, max_work - remaining)))
}

/// The pinned Class.checkOutParam / computeOutLevelParams rules operate on the
/// admitted declaration's original telescope. They do not erase annotations
/// from the type or assume injectivity of any parameter.
pub fn parameters(
    env: &Environment,
    class: &Name,
) -> Result<imported::ClassParameters, InstanceRegistryError> {
    let mut remaining = MAX_ENTRY_BYTES;
    parameters_with_budget(env, class, &mut remaining)
}

fn parameters_with_budget(
    env: &Environment,
    class: &Name,
    work_left: &mut usize,
) -> Result<imported::ClassParameters, InstanceRegistryError> {
    validate_class(env, class)?;
    let info = env.find(class).ok_or(InstanceRegistryError::Malformed)?;
    let mut out = Vec::new();
    let mut domains = Vec::new();
    let mut index = 0u32;
    let mut ty = &info.constant_val().type_;
    loop {
        tick(work_left)?;
        match ty.node() {
            ExprNode::MData { expr, .. } => ty = expr,
            ExprNode::ForallE {
                binder_type,
                body,
                binder_info,
                ..
            } => {
                let mut domain = binder_type;
                while let ExprNode::MData { expr, .. } = domain.node() {
                    tick(work_left)?;
                    domain = expr;
                }
                let annotated = matches!(domain.node(), ExprNode::App { f, .. }
                    if matches!(f.node(), ExprNode::Const { name, .. }
                        if *name == Name::from_components(["outParam"])));
                let mut output = annotated;
                for &previous in &out {
                    tick(work_left)?;
                    if binder_type.has_loose_bvar(index - previous - 1) {
                        if !annotated && *binder_info != BinderInfo::InstImplicit {
                            return Err(InstanceRegistryError::InvalidClass(class.clone()));
                        }
                        output = true;
                    }
                }
                if output {
                    out.push(index);
                } else {
                    domains.push(binder_type);
                }
                index += 1;
                ty = body;
            }
            ExprNode::Sort { .. } => break,
            _ => return Err(InstanceRegistryError::InvalidClass(class.clone())),
        }
    }
    let mut inputs = HashSet::new();
    let mut seen = HashSet::new();
    let mut level_seen = HashSet::new();
    while let Some(expr) = domains.pop() {
        tick(work_left)?;
        if !seen.insert(expr.allocation_identity()) {
            continue;
        }
        let mut levels = Vec::new();
        match expr.node() {
            ExprNode::Sort { level } => levels.push(level),
            ExprNode::Const { levels: values, .. } => levels.extend(values),
            ExprNode::App { f, a } => domains.extend([f, a]),
            ExprNode::ForallE {
                binder_type, body, ..
            }
            | ExprNode::Lam {
                binder_type, body, ..
            } => domains.extend([binder_type, body]),
            ExprNode::LetE {
                type_, value, body, ..
            } => domains.extend([type_, value, body]),
            ExprNode::Proj { expr, .. } | ExprNode::MData { expr, .. } => domains.push(expr),
            _ => {}
        }
        while let Some(level) = levels.pop() {
            tick(work_left)?;
            if !level_seen.insert(std::ptr::from_ref(level)) {
                continue;
            }
            match level.view() {
                LevelView::Param(name) => {
                    inputs.insert(name.clone());
                }
                LevelView::Succ(inner) => levels.push(inner),
                LevelView::Max(a, b) | LevelView::IMax(a, b) => levels.extend([a, b]),
                LevelView::Zero => {}
                LevelView::MVar(_) => return Err(InstanceRegistryError::Malformed),
            }
        }
    }
    // computeOutLevelParams excludes the result sort, even if the class has
    // no term parameters. Do not substitute the source solver's cache policy.
    let out_level_params = info
        .constant_val()
        .level_params
        .iter()
        .enumerate()
        .filter_map(|(i, name)| (!inputs.contains(name)).then_some(i as u32))
        .collect();
    Ok(imported::ClassParameters {
        out_params: out,
        out_level_params,
    })
}

fn tick(left: &mut usize) -> Result<(), InstanceRegistryError> {
    *left = left.checked_sub(1).ok_or(InstanceRegistryError::Limit)?;
    Ok(())
}
