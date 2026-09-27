//! Lexical activation of namespace instances over the native registration journal.
//!
//! The journal stores registrations; an `ActiveScopes` value stores *when* each
//! namespace was opened. Reconstructing the view interleaves those events, so a
//! later global instance can outrank an earlier activation at equal priority.
//! Nothing is inserted into the environment by opening a namespace.
use super::*;
use fln_env::extensions::ExtensionState;

const MAX_SCOPES: usize = 4096;
const MAX_SCOPE_BYTES: usize = 1024 * 1024;

#[derive(Debug, Clone, PartialEq, Eq)]
struct Activation {
    namespace: Name,
    at: usize,
}

/// Immutable-snapshot-friendly lexical state. Its private journal anchor binds
/// every activation position to the exact registration history it observed.
/// Clone it at a section boundary and restore that clone when the section ends.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ActiveScopes {
    activations: Vec<Activation>,
    anchor: Option<ExtensionState>,
    name_bytes: usize,
}
impl ActiveScopes {
    pub fn is_active(&self, namespace: &Name) -> bool {
        self.activations
            .iter()
            .any(|entry| &entry.namespace == namespace)
    }

    pub fn activate(
        &mut self,
        env: &Environment,
        namespace: &Name,
    ) -> Result<(), InstanceRegistryError> {
        self.validate_prefix(env)?;
        // Validate even an empty activation: damaged metadata is not an empty
        // registry, and a failed activation must leave this value unchanged.
        InstanceRegistry::read(env)?;
        if self.is_active(namespace) {
            return Ok(());
        }
        let mut encoded = Vec::new();
        write_name(namespace, &mut encoded)?;
        let bytes = self
            .name_bytes
            .checked_add(encoded.len())
            .filter(|n| *n <= MAX_SCOPE_BYTES)
            .ok_or(InstanceRegistryError::Limit)?;
        if self.activations.len() >= MAX_SCOPES {
            return Err(InstanceRegistryError::Limit);
        }
        let anchor = env.extension(&extension_name()).cloned();
        let at = anchor.as_ref().map_or(0, ExtensionState::len);
        self.activations.push(Activation {
            namespace: namespace.clone(),
            at,
        });
        self.anchor = anchor;
        self.name_bytes = bytes;
        Ok(())
    }

    fn validate_prefix(&self, env: &Environment) -> Result<(), InstanceRegistryError> {
        if let Some(anchor) = &self.anchor {
            let current = env
                .extension(&extension_name())
                .ok_or(InstanceRegistryError::Malformed)?;
            if current.descriptor != anchor.descriptor
                || current.len() < anchor.len()
                || !anchor.entries().zip(current.entries()).all(|(a, b)| a == b)
            {
                return Err(InstanceRegistryError::Malformed);
            }
        }
        Ok(())
    }
}

impl InstanceRegistry {
    /// Read one source scope's candidate view. Ordinary `read` remains the
    /// dormant import view; this function never publishes a global registration.
    pub fn read_with_scopes(
        env: &Environment,
        scopes: &ActiveScopes,
    ) -> Result<Self, InstanceRegistryError> {
        scopes.validate_prefix(env)?;
        let mut registry = Self::read(env)?;
        if scopes.activations.is_empty() {
            return Ok(registry);
        }
        // Event keys are (journal boundary, before/at row, activation-local
        // registration order). One first activation per namespace is retained.
        let mut events = Vec::new();
        for (class, rows) in &registry.instances {
            for row in rows {
                events.push(((row.order, 1u8, 0usize), class.clone(), row.clone()));
            }
        }
        for (activation_index, activation) in scopes.activations.iter().enumerate() {
            let Some(classes) = registry.scoped.get(&activation.namespace) else {
                continue;
            };
            for (class, rows) in classes {
                for row in rows {
                    let key = if row.order < activation.at {
                        // Distinct namespaces may be opened at the same journal
                        // boundary. Preserve the user's activation order, then
                        // each namespace's recorded insertion order.
                        (
                            activation.at,
                            0u8,
                            activation_index * (MAX_ROWS + 1) + row.order,
                        )
                    } else {
                        (row.order, 1u8, 0usize)
                    };
                    events.push((key, class.clone(), row.clone()));
                }
            }
        }
        events.sort_by_key(|(key, _, _)| *key);
        registry.instances.clear();
        for (order, (_, class, mut row)) in events.into_iter().enumerate() {
            row.order = order;
            registry.instances.entry(class).or_default().push(row);
        }
        for rows in registry.instances.values_mut() {
            rows.sort_by(|a, b| {
                b.priority
                    .cmp(&a.priority)
                    .then_with(|| b.order.cmp(&a.order))
            });
        }
        Ok(registry)
    }
}

/// Record a namespace registration over an already admitted declaration. The
/// new tag belongs to the same append-ordered journal as global registrations,
/// so scope activation and subsequent declarations have one chronology.
/// Scope changes and global/scoped promotion are refused, not approximated.
pub fn register(
    env: &Environment,
    namespace: &Name,
    declaration: &Name,
    priority: u32,
) -> Result<Environment, InstanceRegistryError> {
    let registry = InstanceRegistry::read(env)?;
    let class = validate_instance(env, declaration)?;
    if !registry.is_class(&class) {
        return Err(InstanceRegistryError::UnknownClass(class));
    }
    if registry
        .candidates(&class)
        .iter()
        .any(|row| &row.declaration == declaration)
        || registry.scoped.iter().any(|(name, classes)| {
            name != namespace
                && classes
                    .values()
                    .any(|rows| rows.iter().any(|row| &row.declaration == declaration))
        })
    {
        return Err(InstanceRegistryError::DuplicateInstance(
            declaration.clone(),
        ));
    }
    let mut payload = MAGIC.to_vec();
    payload.push(3);
    write_name(&class, &mut payload)?;
    write_name(declaration, &mut payload)?;
    payload.extend(priority.to_le_bytes());
    write_name(namespace, &mut payload)?;
    append(env, payload)
}
