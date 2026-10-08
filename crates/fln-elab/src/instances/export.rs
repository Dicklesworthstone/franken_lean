//! Semantic class metadata for source-module export. No declaration authority.
use super::*;
use fln_core::level::LevelView;
use std::collections::HashSet;

mod data;
mod index;
#[cfg(test)]
mod tests;
pub use data::{InstanceRegistration, Registrations, registrations};

/// Exact pinned indexing metadata for the supported native type fragment.
/// Absence is an explicit unsupported result, never a guessed wildcard path.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DerivedIndex {
    pub keys: Vec<discr_tree::Key>,
    pub synth_order: Vec<u32>,
}

/// Derive indexing without reading the registry again or changing any state.
/// Native source search and artifact export use this same bounded computation.
pub fn derive_index(
    env: &Environment,
    registry: &InstanceRegistry,
    declaration: &Name,
    work_left: &mut usize,
) -> Result<Option<DerivedIndex>, InstanceRegistryError> {
    index::derive(
        env,
        &registry.classes,
        &registry.imported.classes,
        None,
        declaration,
        work_left,
    )
}

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
    Ok(registrations(base, result, max_work)?
        .and_then(|(rows, work)| rows.instances.is_empty().then_some((rows.classes, work))))
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
                    if contains_loose(binder_type, index - previous - 1, work_left)? {
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
    let mut out_level_params = Vec::new();
    for (index, name) in info.constant_val().level_params.iter().enumerate() {
        tick(work_left)?;
        if !inputs.contains(name) {
            out_level_params.push(u32::try_from(index).map_err(|_| InstanceRegistryError::Limit)?);
        }
    }
    Ok(imported::ClassParameters {
        out_params: out,
        out_level_params,
    })
}

fn contains_loose(
    expr: &Expr,
    index: u32,
    left: &mut usize,
) -> Result<bool, InstanceRegistryError> {
    let mut todo = vec![(expr, index)];
    let mut seen = HashSet::new();
    while let Some((expr, index)) = todo.pop() {
        tick(left)?;
        if expr.loose_bvar_range() <= index || !seen.insert((expr.allocation_identity(), index)) {
            continue;
        }
        match expr.node() {
            ExprNode::BVar { idx } if *idx == index => return Ok(true),
            ExprNode::App { f, a } => todo.extend([(f, index), (a, index)]),
            ExprNode::ForallE {
                binder_type, body, ..
            }
            | ExprNode::Lam {
                binder_type, body, ..
            } => {
                todo.extend([(binder_type, index), (body, index.saturating_add(1))]);
            }
            ExprNode::LetE {
                type_, value, body, ..
            } => {
                todo.extend([
                    (type_, index),
                    (value, index),
                    (body, index.saturating_add(1)),
                ]);
            }
            ExprNode::Proj { expr, .. } | ExprNode::MData { expr, .. } => todo.push((expr, index)),
            _ => {}
        }
    }
    Ok(false)
}

fn tick(left: &mut usize) -> Result<(), InstanceRegistryError> {
    *left = left.checked_sub(1).ok_or(InstanceRegistryError::Limit)?;
    Ok(())
}
