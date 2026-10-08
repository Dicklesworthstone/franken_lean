//! Exact ownership and chronological rows of the pinned instance extension.
use super::*;
use fln_core::level::Level;
use std::sync::Arc;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InstanceRegistration {
    pub declaration: Name,
    pub value: Expr,
    pub priority: u32,
    pub synth_order: Vec<u32>,
    pub keys: Vec<discr_tree::Key>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Registrations {
    pub classes: Vec<ClassRegistration>,
    /// Payload bytes examined while checking ownership and imported policies.
    pub bytes_examined: usize,
    /// Chronological registrations, including priority updates. The pin's
    /// DiscrTree replaces an existing value in its original leaf slot.
    pub instances: Vec<InstanceRegistration>,
}

/// Read the exact inherited prefix and module-owned suffix. Every visited row
/// and decoded payload byte consumes work before allocation. An unchanged,
/// shared persistent state returns immediately without inspecting its prefix.
/// `None` refuses the entire operation: scoped registrations, imported-name
/// overrides, or a type outside the exact supported indexing fragment.
pub fn registrations(
    base: &Environment,
    result: &Environment,
    max_work: usize,
) -> Result<Option<(Registrations, usize)>, InstanceRegistryError> {
    let Some(current) = result.extension(&extension_name()) else {
        return if base.extension(&extension_name()).is_some() {
            Err(InstanceRegistryError::Malformed)
        } else {
            Ok(Some((Registrations::default(), 0)))
        };
    };
    if current.descriptor != descriptor() {
        return Err(InstanceRegistryError::Malformed);
    }
    if current.len() > MAX_ROWS {
        return Err(InstanceRegistryError::Limit);
    }
    let prior = base.extension(&extension_name());
    if let Some(prior) = prior {
        if prior.descriptor != current.descriptor || prior.len() > current.len() {
            return Err(InstanceRegistryError::Malformed);
        }
        if std::ptr::eq(prior, current) {
            return Ok(Some((Registrations::default(), 0)));
        }
    }
    let start = prior.map_or(0, |state| state.len());
    let mut old_entries = prior.map(|state| state.entries());
    let mut remaining = max_work;
    let mut classes = BTreeSet::new();
    let mut positions = BTreeMap::<Name, (Name, Option<Name>)>::new();
    let mut exported = Registrations::default();
    let (imported_classes, imported_bytes) = imported::export_classes(result, &mut remaining)?;
    exported.bytes_examined = imported_bytes;
    for (order, entry) in current.entries().enumerate() {
        tick(&mut remaining)?;
        let owned = order >= start;
        if !owned {
            let old = old_entries
                .as_mut()
                .and_then(Iterator::next)
                .ok_or(InstanceRegistryError::Malformed)?;
            if !Arc::ptr_eq(&old.payload, &entry.payload) {
                charge(&mut remaining, old.payload.len())?;
                charge(&mut remaining, entry.payload.len())?;
                exported.bytes_examined += old.payload.len() + entry.payload.len();
                if old != entry {
                    return Err(InstanceRegistryError::Malformed);
                }
            }
        }
        // Read imported class names and existing instance scopes, without
        // re-normalizing every imported declaration as Registry::read would.
        charge(&mut remaining, entry.payload.len())?;
        exported.bytes_examined += entry.payload.len();
        if entry.payload.len() > MAX_ENTRY_BYTES {
            return Err(InstanceRegistryError::Limit);
        }
        let mut bytes = entry
            .payload
            .strip_prefix(MAGIC)
            .ok_or(InstanceRegistryError::Malformed)?;
        let tag = take(&mut bytes, 1)?[0];
        let class = read_name(&mut bytes)?;
        if class.is_anonymous() {
            return Err(InstanceRegistryError::Malformed);
        }
        if tag == 0 {
            if !bytes.is_empty() || !classes.insert(class.clone()) {
                return Err(InstanceRegistryError::Malformed);
            }
            validate_class(result, &class)?;
            if owned {
                if base.contains(&class) {
                    return Ok(None);
                }
                let parameters = match imported_classes.get(&class) {
                    Some(parameters) => {
                        charge(
                            &mut remaining,
                            parameters.out_params.len() + parameters.out_level_params.len(),
                        )?;
                        parameters.clone()
                    }
                    None => parameters_with_budget(result, &class, &mut remaining)?,
                };
                exported.classes.push(ClassRegistration {
                    name: class,
                    parameters,
                });
            } else if !base.contains(&class) {
                return Err(InstanceRegistryError::Malformed);
            }
            continue;
        }
        if !(1..=3).contains(&tag) || !classes.contains(&class) {
            return Err(InstanceRegistryError::Malformed);
        }
        let declaration = read_name(&mut bytes)?;
        let priority = u32::from_le_bytes(
            take(&mut bytes, 4)?
                .try_into()
                .map_err(|_| InstanceRegistryError::Malformed)?,
        );
        let scope = if tag == 3 {
            Some(read_name(&mut bytes)?)
        } else {
            None
        };
        if !bytes.is_empty()
            || declaration.is_anonymous()
            || scope.as_ref().is_some_and(Name::is_anonymous)
            || !result.contains(&declaration)
        {
            return Err(InstanceRegistryError::Malformed);
        }
        if owned && (base.contains(&declaration) || scope.is_some()) {
            return Ok(None);
        }
        if !owned && !base.contains(&declaration) {
            return Err(InstanceRegistryError::Malformed);
        }
        if let Some((old_class, old_scope)) = positions.get(&declaration) {
            if tag == 1 || old_class != &class || old_scope != &scope {
                return Err(InstanceRegistryError::Malformed);
            }
        } else {
            positions.insert(declaration.clone(), (class.clone(), scope));
        }
        if !owned {
            continue;
        }
        // Derive against the class registrations visible at THIS journal row.
        // A later `[class]` registration must not rewrite an earlier key.
        let Some(derived) = index::derive(
            result,
            &classes,
            &imported_classes,
            Some(&class),
            &declaration,
            &mut remaining,
        )?
        else {
            return Ok(None);
        };
        let info = result
            .find(&declaration)
            .ok_or(InstanceRegistryError::Malformed)?;
        charge(&mut remaining, info.constant_val().level_params.len())?;
        let value = Expr::const_(
            declaration.clone(),
            info.constant_val()
                .level_params
                .iter()
                .cloned()
                .map(Level::param)
                .collect(),
        );
        exported.instances.push(InstanceRegistration {
            declaration,
            value,
            priority,
            synth_order: derived.synth_order,
            keys: derived.keys,
        });
    }
    // Source search derives supported native models from the final registry.
    // Refuse a later class registration that would change an earlier stored
    // path or schedule, rather than letting artifact reimport select a different
    // dictionary. Inherited-name class changes were already refused above.
    let mut final_models = BTreeMap::new();
    for row in &exported.instances {
        tick(&mut remaining)?;
        if !final_models.contains_key(&row.declaration) {
            let Some(model) = index::derive(
                result,
                &classes,
                &imported_classes,
                None,
                &row.declaration,
                &mut remaining,
            )?
            else {
                return Ok(None);
            };
            final_models.insert(row.declaration.clone(), model);
        }
        let model = &final_models[&row.declaration];
        charge(&mut remaining, row.keys.len() + row.synth_order.len())?;
        if model.keys != row.keys || model.synth_order != row.synth_order {
            return Ok(None);
        }
    }
    Ok(Some((exported, max_work - remaining)))
}

fn charge(remaining: &mut usize, amount: usize) -> Result<(), InstanceRegistryError> {
    *remaining = remaining
        .checked_sub(amount)
        .ok_or(InstanceRegistryError::Limit)?;
    Ok(())
}
