//! Metered ownership and result-head validation for default registrations.
use super::*;
use crate::instances;

struct Meter {
    remaining: usize,
    bytes_examined: usize,
}

impl Meter {
    fn charge(&mut self, amount: usize) -> Result<(), InstanceRegistryError> {
        self.remaining = self
            .remaining
            .checked_sub(amount)
            .ok_or(InstanceRegistryError::Limit)?;
        Ok(())
    }

    fn payload(&mut self, payload: &[u8]) -> Result<(), InstanceRegistryError> {
        if payload.len() > MAX_ENTRY_BYTES {
            return Err(InstanceRegistryError::Limit);
        }
        self.charge(payload.len())?;
        self.bytes_examined = self
            .bytes_examined
            .checked_add(payload.len())
            .ok_or(InstanceRegistryError::Limit)?;
        Ok(())
    }
}

pub(super) fn registrations(
    base: &Environment,
    result: &Environment,
    max_work: usize,
) -> Result<Registrations, InstanceRegistryError> {
    let prior = base.extension(&name());
    let Some(current) = result.extension(&name()) else {
        return if prior.is_some() {
            Err(InstanceRegistryError::Malformed)
        } else {
            Ok(Registrations::default())
        };
    };
    if current.descriptor != descriptor() {
        return Err(InstanceRegistryError::Malformed);
    }
    if current.len() > MAX_ROWS {
        return Err(InstanceRegistryError::Limit);
    }
    if let Some(prior) = prior {
        if prior.descriptor != current.descriptor || prior.len() > current.len() {
            return Err(InstanceRegistryError::Malformed);
        }
        if std::ptr::eq(prior, current) {
            return Ok(Registrations::default());
        }
    }
    let start = prior.map_or(0, |state| state.len());
    let mut inherited = prior.map(|state| state.entries());
    let mut meter = Meter {
        remaining: max_work,
        bytes_examined: 0,
    };
    let mut suffix = Vec::new();
    for (order, entry) in current.entries().enumerate() {
        meter.charge(1)?;
        if order < start {
            let old = inherited
                .as_mut()
                .and_then(Iterator::next)
                .ok_or(InstanceRegistryError::Malformed)?;
            if !std::sync::Arc::ptr_eq(&old.payload, &entry.payload) {
                meter.payload(&old.payload)?;
                meter.payload(&entry.payload)?;
                if old != entry {
                    return Err(InstanceRegistryError::Malformed);
                }
            }
            continue;
        }
        meter.payload(&entry.payload)?;
        let mut bytes = entry
            .payload
            .strip_prefix(DEFAULT_MAGIC)
            .ok_or(InstanceRegistryError::Malformed)?;
        let declaration = read_name(&mut bytes)?;
        let priority = u32::from_le_bytes(
            take(&mut bytes, 4)?
                .try_into()
                .map_err(|_| InstanceRegistryError::Malformed)?,
        );
        if !bytes.is_empty() {
            return Err(InstanceRegistryError::Malformed);
        }
        suffix.push(InstanceEntry {
            declaration,
            priority,
            order,
        });
    }
    let mut entries = Vec::new();
    if !suffix.is_empty() {
        let classes = class_memberships(result, &mut meter)?;
        let mut checked = BTreeMap::new();
        for candidate in suffix {
            meter.charge(1)?;
            let class = match checked.get(&candidate.declaration) {
                Some(class) => Name::clone(class),
                None => {
                    let class = candidate_class(result, &candidate.declaration, &mut meter)?;
                    if !classes.contains(&class) {
                        return Err(InstanceRegistryError::UnknownClass(class));
                    }
                    checked.insert(candidate.declaration.clone(), class.clone());
                    class
                }
            };
            entries.push(DefaultInstance { class, candidate });
        }
    }
    Ok(Registrations {
        entries,
        work: max_work - meter.remaining,
        bytes_examined: meter.bytes_examined,
    })
}

/// Read class membership and journal shape without normalizing unrelated
/// ordinary/imported candidates. Their declarations were already admitted;
/// exporting a default neither owns nor changes their search metadata.
fn class_memberships(
    env: &Environment,
    meter: &mut Meter,
) -> Result<BTreeSet<Name>, InstanceRegistryError> {
    let mut classes = BTreeSet::new();
    if let Some(extension) = env.extension(&instances::extension_name()) {
        if extension.descriptor != instances::descriptor() {
            return Err(InstanceRegistryError::Malformed);
        }
        if extension.len() > MAX_ROWS {
            return Err(InstanceRegistryError::Limit);
        }
        let mut positions = BTreeMap::<Name, (Name, Option<Name>)>::new();
        for entry in extension.entries() {
            meter.charge(1)?;
            meter.payload(&entry.payload)?;
            let mut bytes = entry
                .payload
                .strip_prefix(instances::MAGIC)
                .ok_or(InstanceRegistryError::Malformed)?;
            let tag = take(&mut bytes, 1)?[0];
            let class = read_name(&mut bytes)?;
            if tag == 0 {
                if !bytes.is_empty() || !classes.insert(class.clone()) {
                    return Err(InstanceRegistryError::Malformed);
                }
                validate_class(env, &class)?;
                continue;
            }
            if !(1..=3).contains(&tag) || !classes.contains(&class) {
                return Err(InstanceRegistryError::Malformed);
            }
            let declaration = read_name(&mut bytes)?;
            take(&mut bytes, 4)?;
            let scope = if tag == 3 {
                Some(read_name(&mut bytes)?)
            } else {
                None
            };
            if !bytes.is_empty() || !env.contains(&declaration) {
                return Err(InstanceRegistryError::Malformed);
            }
            if let Some((old_class, old_scope)) = positions.get(&declaration) {
                if tag == 1 || old_class != &class || old_scope != &scope {
                    return Err(InstanceRegistryError::Malformed);
                }
            } else {
                positions.insert(declaration, (class, scope));
            }
        }
    }
    let (imported, bytes) = instances::imported::export_classes(env, &mut meter.remaining)?;
    meter.bytes_examined = meter
        .bytes_examined
        .checked_add(bytes)
        .ok_or(InstanceRegistryError::Limit)?;
    for class in imported.keys() {
        meter.charge(1)?;
        if !classes.contains(class) {
            return Err(InstanceRegistryError::UnknownClass(class.clone()));
        }
    }
    Ok(classes)
}

#[derive(Clone)]
struct Closure {
    expr: Expr,
    scope: Option<usize>,
}

struct Binding {
    value: Option<Closure>,
    outer: Option<usize>,
}

/// The abbreviation-transparent telescope head, evaluated by a small closure
/// machine. Only demanded nodes are visited. Every application, binder,
/// unfolding and variable lookup consumes work before allocation; there is no
/// unmetered substitution into a potentially large shared expression DAG.
/// Scope links live in an arena, so deep telescopes do not recurse on drop.
fn candidate_class(
    env: &Environment,
    declaration: &Name,
    meter: &mut Meter,
) -> Result<Name, InstanceRegistryError> {
    meter.charge(1)?;
    let info = env
        .find(declaration)
        .ok_or_else(|| InstanceRegistryError::UnknownDeclaration(declaration.clone()))?;
    let safe = match info {
        ConstantInfo::Defn(value) => value.safety == DefinitionSafety::Safe,
        ConstantInfo::Thm(_) => true,
        ConstantInfo::Opaque(value) => !value.is_unsafe,
        ConstantInfo::Axiom(value) => !value.is_unsafe,
        ConstantInfo::Ctor(value) => !value.is_unsafe,
        _ => false,
    };
    let invalid = || InstanceRegistryError::InvalidInstance(declaration.clone());
    if !safe {
        return Err(invalid());
    }
    let mut current = Closure {
        expr: info.constant_val().type_.clone(),
        scope: None,
    };
    let mut arguments = Vec::<Closure>::new();
    let mut bindings = Vec::<Binding>::new();
    loop {
        meter.charge(1)?;
        match current.expr.node() {
            ExprNode::App { f, a } => {
                arguments.push(Closure {
                    expr: a.clone(),
                    scope: current.scope,
                });
                current.expr = f.clone();
            }
            ExprNode::MData { expr, .. } => current.expr = expr.clone(),
            ExprNode::ForallE { body, .. } if arguments.is_empty() => {
                let scope = bindings.len();
                bindings.push(Binding {
                    value: None,
                    outer: current.scope,
                });
                current = Closure {
                    expr: body.clone(),
                    scope: Some(scope),
                };
            }
            ExprNode::Lam { body, .. } => {
                let argument = arguments.pop().ok_or_else(invalid)?;
                let scope = bindings.len();
                bindings.push(Binding {
                    value: Some(argument),
                    outer: current.scope,
                });
                current = Closure {
                    expr: body.clone(),
                    scope: Some(scope),
                };
            }
            ExprNode::Const { name, levels } => {
                match env.find(name) {
                    Some(ConstantInfo::Defn(definition))
                        if definition.safety == DefinitionSafety::Safe
                            && definition.hints == ReducibilityHints::Abbrev
                            && definition.base.level_params.len() == levels.len() =>
                    {
                        // Universe substitution cannot change the class head.
                        current = Closure {
                            expr: definition.value.clone(),
                            scope: None,
                        };
                    }
                    _ => return Ok(name.clone()),
                }
            }
            ExprNode::BVar { idx } => {
                let mut index = *idx;
                let mut scope = current.scope;
                loop {
                    meter.charge(1)?;
                    let binding = scope
                        .and_then(|slot| bindings.get(slot))
                        .ok_or_else(invalid)?;
                    if index == 0 {
                        current = binding.value.as_ref().cloned().ok_or_else(invalid)?;
                        break;
                    }
                    index -= 1;
                    scope = binding.outer;
                }
            }
            _ => return Err(invalid()),
        }
    }
}

#[cfg(test)]
mod tests;
