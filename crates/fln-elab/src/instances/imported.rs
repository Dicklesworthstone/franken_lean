//! Search metadata for already checked foreign declarations. This journal is
//! native data, not an admission path or an interpreter for foreign code.
//!
//! Explicit output universes can differ from those inferred from a class type
//! (`univ_out_params`), and prerequisite order belongs to an instance, not its
//! caller. Retain both instead of silently replacing them with local defaults.
use super::*;
use fln_core::expr::BinderInfo;

const MAGIC: &[u8] = b"FLNIMPI\x01";

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ClassParameters {
    pub out_params: Vec<u32>,
    pub out_level_params: Vec<u32>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InstanceParameters {
    pub priority: u32,
    /// Absolute positions in the declaration's forall telescope.
    pub synth_order: Vec<u32>,
    /// A scoped registration is retained but is not an ordinary global instance.
    pub scope: Option<Name>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(super) struct Metadata {
    pub classes: BTreeMap<Name, ClassParameters>,
    pub instances: BTreeMap<Name, InstanceParameters>,
}

fn name() -> Name {
    Name::from_components(["FrankenLean", "importedInstances", "v1"])
}
fn descriptor() -> ExtensionDescriptor {
    ExtensionDescriptor {
        name: name(),
        merge: MergeSemantics::AppendOrdered,
        checkpoint: CheckpointSemantics::FullJournal,
        provenance: PayloadProvenance::Understood,
    }
}

fn indices(bytes: &mut &[u8]) -> Result<Vec<u32>, InstanceRegistryError> {
    let count = u32::from_le_bytes(
        take(bytes, 4)?
            .try_into()
            .map_err(|_| InstanceRegistryError::Malformed)?,
    );
    let size = usize::try_from(count)
        .ok()
        .and_then(|n| n.checked_mul(4))
        .ok_or(InstanceRegistryError::Limit)?;
    // Prove the entire storage fits before allocating from its encoded length.
    let data = take(bytes, size)?;
    let mut seen = BTreeSet::new();
    let mut values = Vec::with_capacity(data.len() / 4);
    for chunk in data.as_chunks::<4>().0 {
        let value = u32::from_le_bytes(*chunk);
        if !seen.insert(value) {
            return Err(InstanceRegistryError::Malformed);
        }
        values.push(value);
    }
    Ok(values)
}
fn write_indices(values: &[u32], bytes: &mut Vec<u8>) -> Result<(), InstanceRegistryError> {
    let added = values
        .len()
        .checked_mul(4)
        .and_then(|n| n.checked_add(4))
        .ok_or(InstanceRegistryError::Limit)?;
    if bytes.len().saturating_add(added) > MAX_ENTRY_BYTES {
        return Err(InstanceRegistryError::Limit);
    }
    bytes.extend(
        u32::try_from(values.len())
            .map_err(|_| InstanceRegistryError::Limit)?
            .to_le_bytes(),
    );
    for value in values {
        bytes.extend(value.to_le_bytes());
    }
    Ok(())
}

fn telescope(info: &ConstantInfo) -> Result<Vec<BinderInfo>, InstanceRegistryError> {
    let mut current = &info.constant_val().type_;
    let mut binders = Vec::new();
    for _ in 0..MAX_ENTRY_BYTES {
        match current.node() {
            ExprNode::ForallE {
                binder_info, body, ..
            } => {
                binders.push(*binder_info);
                current = body;
            }
            ExprNode::MData { expr, .. } => current = expr,
            _ => return Ok(binders),
        }
    }
    Err(InstanceRegistryError::Limit)
}
fn validate_indices(values: &[u32], bound: usize) -> Result<(), InstanceRegistryError> {
    let mut seen = BTreeSet::new();
    for value in values {
        if usize::try_from(*value).map_or(true, |v| v >= bound) || !seen.insert(*value) {
            return Err(InstanceRegistryError::Malformed);
        }
    }
    Ok(())
}
fn validate_parameters(
    env: &Environment,
    class: &Name,
    parameters: &ClassParameters,
) -> Result<(), InstanceRegistryError> {
    validate_class(env, class)?;
    let info = env
        .find(class)
        .ok_or_else(|| InstanceRegistryError::UnknownDeclaration(class.clone()))?;
    validate_indices(&parameters.out_params, telescope(info)?.len())?;
    validate_indices(
        &parameters.out_level_params,
        info.constant_val().level_params.len(),
    )
}
fn validate_order(
    env: &Environment,
    declaration: &Name,
    parameters: &InstanceParameters,
) -> Result<(), InstanceRegistryError> {
    validate_instance(env, declaration)?;
    let info = env
        .find(declaration)
        .ok_or_else(|| InstanceRegistryError::UnknownDeclaration(declaration.clone()))?;
    // Synthesis positions index the Reference's reducing telescope
    // (computeSynthOrder), so an abbreviation's binders count too.
    let (binders, _) = instance_telescope(env, &info.constant_val().type_)
        .ok_or_else(|| InstanceRegistryError::InvalidInstance(declaration.clone()))?;
    validate_indices(&parameters.synth_order, binders.len())?;
    let expected: Vec<_> = binders
        .iter()
        .enumerate()
        .filter_map(|(i, binder)| (*binder == BinderInfo::InstImplicit).then_some(i))
        .collect();
    if parameters.synth_order.len() != expected.len()
        || parameters
            .synth_order
            .iter()
            .any(|i| !expected.contains(&(*i as usize)))
        || parameters.scope.as_ref().is_some_and(Name::is_anonymous)
    {
        return Err(InstanceRegistryError::Malformed);
    }
    Ok(())
}

/// The imported-instance journal's content identity, if the journal exists.
pub(super) fn journal_digest(env: &Environment) -> Option<[u8; 32]> {
    env.extension(&name())
        .map(|extension| extension.content_digest().0)
}

pub(super) fn read(env: &Environment) -> Result<Metadata, InstanceRegistryError> {
    let Some(extension) = env.extension(&name()) else {
        return Ok(Metadata::default());
    };
    if extension.descriptor != descriptor() {
        return Err(InstanceRegistryError::Malformed);
    }
    if extension.len() > MAX_ROWS {
        return Err(InstanceRegistryError::Limit);
    }
    let mut result = Metadata::default();
    for entry in extension.entries() {
        result.apply(env, &entry.payload)?;
    }
    Ok(result)
}

impl Metadata {
    /// Validate one journal row and fold it in, as [`read`] does for each row in
    /// journal order. A later row for a name replaces the earlier one.
    fn apply(&mut self, env: &Environment, payload: &[u8]) -> Result<(), InstanceRegistryError> {
        if payload.len() > MAX_ENTRY_BYTES {
            return Err(InstanceRegistryError::Limit);
        }
        let mut bytes: &[u8] = payload;
        if take(&mut bytes, MAGIC.len())? != MAGIC {
            return Err(InstanceRegistryError::Malformed);
        }
        let tag = take(&mut bytes, 1)?[0];
        let declaration = read_name(&mut bytes)?;
        match tag {
            0 => {
                let parameters = ClassParameters {
                    out_params: indices(&mut bytes)?,
                    out_level_params: indices(&mut bytes)?,
                };
                validate_parameters(env, &declaration, &parameters)?;
                self.classes.insert(declaration, parameters);
            }
            1 => {
                let priority = u32::from_le_bytes(
                    take(&mut bytes, 4)?
                        .try_into()
                        .map_err(|_| InstanceRegistryError::Malformed)?,
                );
                let scope = match take(&mut bytes, 1)?[0] {
                    0 => None,
                    1 => Some(read_name(&mut bytes)?),
                    _ => return Err(InstanceRegistryError::Malformed),
                };
                let parameters = InstanceParameters {
                    priority,
                    scope,
                    synth_order: indices(&mut bytes)?,
                };
                validate_order(env, &declaration, &parameters)?;
                self.instances.insert(declaration, parameters);
            }
            _ => return Err(InstanceRegistryError::Malformed),
        }
        if !bytes.is_empty() {
            return Err(InstanceRegistryError::Malformed);
        }
        Ok(())
    }
}

/// This journal's row for a class (tag 0).
fn class_metadata_payload(
    class: &Name,
    parameters: &ClassParameters,
) -> Result<Vec<u8>, InstanceRegistryError> {
    let mut payload = MAGIC.to_vec();
    payload.push(0);
    write_name(class, &mut payload)?;
    write_indices(&parameters.out_params, &mut payload)?;
    write_indices(&parameters.out_level_params, &mut payload)?;
    Ok(payload)
}

/// This journal's row for an instance (tag 1).
fn instance_metadata_payload(
    declaration: &Name,
    parameters: &InstanceParameters,
) -> Result<Vec<u8>, InstanceRegistryError> {
    let mut payload = MAGIC.to_vec();
    payload.push(1);
    write_name(declaration, &mut payload)?;
    payload.extend(parameters.priority.to_le_bytes());
    payload.push(u8::from(parameters.scope.is_some()));
    if let Some(scope) = &parameters.scope {
        write_name(scope, &mut payload)?;
    }
    write_indices(&parameters.synth_order, &mut payload)?;
    Ok(payload)
}

fn append(env: &Environment, payload: Vec<u8>) -> Result<Environment, InstanceRegistryError> {
    if payload.len() > MAX_ENTRY_BYTES {
        return Err(InstanceRegistryError::Limit);
    }
    let env = if env.extension(&name()).is_none() {
        env.register_extension(descriptor())
            .map_err(|_| InstanceRegistryError::Malformed)?
    } else {
        env.clone()
    };
    if env
        .extension(&name())
        .is_some_and(|extension| extension.len() >= MAX_ROWS)
    {
        return Err(InstanceRegistryError::Limit);
    }
    env.push_extension_entry(&name(), payload)
        .map_err(|_| InstanceRegistryError::Malformed)
}

/// Activate class metadata only over an existing admitted class declaration.
/// Later journal entries replace earlier metadata, as the foreign extension does.
pub fn register_class(
    env: &Environment,
    class: &Name,
    parameters: &ClassParameters,
) -> Result<Environment, InstanceRegistryError> {
    validate_parameters(env, class, parameters)?;
    let env = super::register_class(env, class)?;
    append(&env, class_metadata_payload(class, parameters)?)
}

/// Preserve the foreign prerequisite permutation and priority. Scoped entries
/// remain dormant; importing them must never grant global instance visibility.
pub fn register_instance(
    env: &Environment,
    declaration: &Name,
    parameters: &InstanceParameters,
) -> Result<Environment, InstanceRegistryError> {
    validate_order(env, declaration, parameters)?;
    let registry = InstanceRegistry::read(env)?;
    let class = validate_instance(env, declaration)?;
    if !registry.is_class(&class) {
        return Err(InstanceRegistryError::UnknownClass(class));
    }
    let env = if let Some(scope) = &parameters.scope {
        if registry
            .candidates(&class)
            .iter()
            .any(|entry| &entry.declaration == declaration)
        {
            // Do not leave an earlier global registration visible after a scope
            // change. Scope-changing erasure requires a separate journal event.
            return Err(InstanceRegistryError::DuplicateInstance(
                declaration.clone(),
            ));
        }
        super::scoped::register(env, scope, declaration, parameters.priority)?
    } else {
        super::set_instance(env, declaration, parameters.priority)?
    };
    append(&env, instance_metadata_payload(declaration, parameters)?)
}

/// Activation of an import's class, instance and default-instance journals while
/// its admitted constants stay fixed (bead `fln-uyuz`).
///
/// Row by row this is [`register_class`], [`register_instance`] and
/// [`super::defaults::register`]: the same checks, in the same order, against the
/// same journal state, appending the same rows in the same order. It differs only
/// in keeping that state. Those functions re-read and re-validate every earlier row
/// on each call (including an `instance_telescope` per instance), which made
/// activating the pinned `Init` closure quadratic in its instances.
///
/// Re-reading cannot change an answer here. The constants do not change while this
/// runs, so a row validated once stays valid, and every registration accepted here
/// leaves the journals in a state [`InstanceRegistry::read`] accepts. [`Self::finish`]
/// still reads each journal it touched once, so a disagreement between the kept
/// state and the journals is refused, never trusted.
///
/// Each step consumes the activation: an error drops it, exactly as an error from
/// the per-call functions leaves the caller with no successor environment.
#[derive(Debug)]
pub struct ImportActivation {
    env: Environment,
    registry: Option<(InstanceRegistry, super::Positions)>,
    defaults: Option<Vec<Name>>,
}

/// The ordinary registry as [`InstanceRegistry::read`] would find it in `env`,
/// read on first use.
fn kept<'a>(
    slot: &'a mut Option<(InstanceRegistry, super::Positions)>,
    env: &Environment,
) -> Result<&'a mut (InstanceRegistry, super::Positions), InstanceRegistryError> {
    match slot {
        Some(kept) => Ok(kept),
        None => Ok(slot.insert(InstanceRegistry::read_unsorted(env)?)),
    }
}

/// How many rows the ordinary registry journal holds: the next row's order.
fn ordinary_rows(env: &Environment) -> usize {
    env.extension(&super::extension_name())
        .map_or(0, |state| state.len())
}

impl ImportActivation {
    pub fn new(env: Environment) -> Self {
        Self {
            env,
            registry: None,
            defaults: None,
        }
    }

    /// The environment with every registration so far.
    pub fn environment(&self) -> &Environment {
        &self.env
    }

    /// [`register_class`].
    pub fn register_class(
        mut self,
        class: &Name,
        parameters: &ClassParameters,
    ) -> Result<Self, InstanceRegistryError> {
        validate_parameters(&self.env, class, parameters)?;
        let (registry, positions) = kept(&mut self.registry, &self.env)?;
        validate_class(&self.env, class)?;
        let mut env = self.env.clone();
        if !registry.is_class(class) {
            let order = ordinary_rows(&env);
            let row = super::class_payload(class)?;
            env = super::append(&env, row.clone())?;
            registry.apply_row(&env, positions, order, &row)?;
        }
        let row = class_metadata_payload(class, parameters)?;
        env = append(&env, row.clone())?;
        registry.imported.apply(&env, &row)?;
        self.env = env;
        Ok(self)
    }

    /// [`register_instance`].
    pub fn register_instance(
        mut self,
        declaration: &Name,
        parameters: &InstanceParameters,
    ) -> Result<Self, InstanceRegistryError> {
        validate_order(&self.env, declaration, parameters)?;
        let (registry, positions) = kept(&mut self.registry, &self.env)?;
        let class = validate_instance(&self.env, declaration)?;
        if !registry.is_class(&class) {
            return Err(InstanceRegistryError::UnknownClass(class));
        }
        let listed = |registry: &InstanceRegistry| {
            registry
                .candidates(&class)
                .iter()
                .any(|entry| &entry.declaration == declaration)
        };
        let (tag, scope) = match &parameters.scope {
            Some(scope) => {
                // `register_instance`'s own check, then `scoped::register`'s.
                if listed(registry)
                    || registry.scoped.iter().any(|(name, classes)| {
                        name != scope
                            && classes
                                .values()
                                .any(|rows| rows.iter().any(|row| &row.declaration == declaration))
                    })
                {
                    return Err(InstanceRegistryError::DuplicateInstance(
                        declaration.clone(),
                    ));
                }
                (3, Some(scope))
            }
            // `set_instance`'s check: a global registration may be upserted.
            None => {
                if registry.is_scoped_instance(declaration) {
                    return Err(InstanceRegistryError::DuplicateInstance(
                        declaration.clone(),
                    ));
                }
                (2, None)
            }
        };
        let order = ordinary_rows(&self.env);
        let row = super::instance_payload(tag, &class, declaration, parameters.priority, scope)?;
        let mut env = super::append(&self.env, row.clone())?;
        registry.apply_row(&env, positions, order, &row)?;
        let row = instance_metadata_payload(declaration, parameters)?;
        env = append(&env, row.clone())?;
        registry.imported.apply(&env, &row)?;
        self.env = env;
        Ok(self)
    }

    /// [`super::defaults::register`].
    pub fn register_default(
        mut self,
        declaration: &Name,
        priority: u32,
    ) -> Result<Self, InstanceRegistryError> {
        let existing = match &mut self.defaults {
            Some(existing) => existing,
            None => self.defaults.insert(
                super::defaults::read(&self.env)?
                    .into_iter()
                    .map(|row| row.candidate.declaration)
                    .collect(),
            ),
        };
        if existing.len() >= MAX_ROWS {
            return Err(InstanceRegistryError::Limit);
        }
        if existing.contains(declaration) {
            return Err(InstanceRegistryError::DuplicateInstance(
                declaration.clone(),
            ));
        }
        let class = validate_instance(&self.env, declaration)?;
        let (registry, _) = kept(&mut self.registry, &self.env)?;
        if !registry.is_class(&class) {
            return Err(InstanceRegistryError::UnknownClass(class));
        }
        self.env = super::defaults::append(&self.env, declaration, priority)?;
        existing.push(declaration.clone());
        Ok(self)
    }

    /// The activated environment, once each journal touched has been read back
    /// whole and found to agree.
    pub fn finish(self) -> Result<Environment, InstanceRegistryError> {
        if self.registry.is_some() {
            InstanceRegistry::read(&self.env)?;
        }
        if self.defaults.is_some() {
            super::defaults::read(&self.env)?;
        }
        Ok(self.env)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn malformed_metadata_cannot_be_hidden_by_a_missing_ordinary_registry() {
        for bytes in [vec![], MAGIC.to_vec(), [MAGIC, &[9]].concat()] {
            let env = Environment::new()
                .register_extension(descriptor())
                .unwrap()
                .push_extension_entry(&name(), bytes)
                .unwrap();
            assert!(InstanceRegistry::read(&env).is_err());
        }
        let mut foreign = descriptor();
        foreign.provenance = PayloadProvenance::Opaque;
        let env = Environment::new().register_extension(foreign).unwrap();
        assert!(InstanceRegistry::read(&env).is_err());
    }

    #[test]
    fn encoded_index_counts_are_checked_before_allocation() {
        let bytes = u32::MAX.to_le_bytes();
        assert!(indices(&mut bytes.as_slice()).is_err());
        let mut bytes = Vec::new();
        write_indices(&[2, 0, 1], &mut bytes).unwrap();
        assert_eq!(indices(&mut bytes.as_slice()).unwrap(), [2, 0, 1]);
        let mut duplicate = Vec::new();
        write_indices(&[1, 1], &mut duplicate).unwrap();
        assert!(indices(&mut duplicate.as_slice()).is_err());
    }
}
