//! Default candidates have a separate immutable journal and separate priorities.
//! They may fix unknown inputs only at the final synthesis phase. Registering a
//! default never manufactures a declaration or changes ordinary search order.
use super::*;

const DEFAULT_MAGIC: &[u8] = b"FLNDEFI\x01";
fn name() -> Name {
    Name::from_components(["FrankenLean", "sourceDefaultInstances", "v1"])
}
fn descriptor() -> ExtensionDescriptor {
    ExtensionDescriptor {
        name: name(),
        merge: MergeSemantics::AppendOrdered,
        checkpoint: CheckpointSemantics::FullJournal,
        provenance: PayloadProvenance::Understood,
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DefaultInstance {
    pub class: Name,
    pub candidate: InstanceEntry,
}

pub fn read(env: &Environment) -> Result<Vec<DefaultInstance>, InstanceRegistryError> {
    let Some(extension) = env.extension(&name()) else {
        return Ok(Vec::new());
    };
    if extension.descriptor != descriptor() {
        return Err(InstanceRegistryError::Malformed);
    }
    if extension.len() > MAX_ROWS {
        return Err(InstanceRegistryError::Limit);
    }
    let registry = InstanceRegistry::read(env)?;
    let mut seen = BTreeSet::new();
    let mut result = Vec::new();
    for (order, entry) in extension.entries().enumerate() {
        if entry.payload.len() > MAX_ENTRY_BYTES {
            return Err(InstanceRegistryError::Limit);
        }
        let mut bytes: &[u8] = &entry.payload;
        if take(&mut bytes, DEFAULT_MAGIC.len())? != DEFAULT_MAGIC {
            return Err(InstanceRegistryError::Malformed);
        }
        let declaration = read_name(&mut bytes)?;
        let priority = u32::from_le_bytes(
            take(&mut bytes, 4)?
                .try_into()
                .map_err(|_| InstanceRegistryError::Malformed)?,
        );
        if !bytes.is_empty() || !seen.insert(declaration.clone()) {
            return Err(InstanceRegistryError::Malformed);
        }
        let class = validate_instance(env, &declaration)?;
        if !registry.is_class(&class) {
            return Err(InstanceRegistryError::UnknownClass(class));
        }
        result.push(DefaultInstance {
            class,
            candidate: InstanceEntry {
                declaration,
                priority,
                order,
            },
        });
    }
    result.sort_by(|a, b| {
        b.candidate
            .priority
            .cmp(&a.candidate.priority)
            .then_with(|| b.candidate.order.cmp(&a.candidate.order))
    });
    Ok(result)
}

/// Add an already admitted, safe default candidate. This does not register it
/// as an ordinary instance; callers can independently opt into both phases.
pub fn register(
    env: &Environment,
    declaration: &Name,
    priority: u32,
) -> Result<Environment, InstanceRegistryError> {
    let existing = read(env)?;
    if existing.len() >= MAX_ROWS {
        return Err(InstanceRegistryError::Limit);
    }
    if existing
        .iter()
        .any(|row| &row.candidate.declaration == declaration)
    {
        return Err(InstanceRegistryError::DuplicateInstance(
            declaration.clone(),
        ));
    }
    let class = validate_instance(env, declaration)?;
    if !InstanceRegistry::read(env)?.is_class(&class) {
        return Err(InstanceRegistryError::UnknownClass(class));
    }
    let mut payload = DEFAULT_MAGIC.to_vec();
    write_name(declaration, &mut payload)?;
    payload.extend(priority.to_le_bytes());
    if payload.len() > MAX_ENTRY_BYTES {
        return Err(InstanceRegistryError::Limit);
    }
    let env = if env.extension(&name()).is_none() {
        env.register_extension(descriptor())
            .map_err(|_| InstanceRegistryError::Malformed)?
    } else {
        env.clone()
    };
    env.push_extension_entry(&name(), payload)
        .map_err(|_| InstanceRegistryError::Malformed)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn missing_declarations_and_malformed_default_journals_are_refused() {
        let env = Environment::new();
        assert!(register(&env, &Name::from_components(["missing"]), 100).is_err());
        for payload in [vec![], DEFAULT_MAGIC.to_vec(), b"FLNDEFI\x02".to_vec()] {
            let env = env
                .register_extension(descriptor())
                .unwrap()
                .push_extension_entry(&name(), payload)
                .unwrap();
            assert!(read(&env).is_err());
        }
    }
}
