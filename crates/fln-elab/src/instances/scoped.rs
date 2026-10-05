//! Lexical activation of namespace instances over the native registration journal.
//!
//! The journal stores registrations; an `ActiveScopes` value stores *when* each
//! namespace was opened. Reconstructing the view interleaves those events, so a
//! later global instance can outrank an earlier activation at equal priority.
//! Nothing is inserted into the environment by opening a namespace.
use super::*;
use fln_env::extensions::ExtensionState;
use std::sync::Arc;

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
    activations: Arc<Vec<Activation>>,
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
        Arc::make_mut(&mut self.activations).push(Activation {
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
    append(
        env,
        instance_payload(3, &class, declaration, priority, Some(namespace))?,
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn activation_limits_are_failure_atomic_and_snapshots_share_their_history() {
        let env = Environment::new();
        let mut active = ActiveScopes::default();
        for index in 0..MAX_SCOPES {
            active
                .activate(&env, &Name::num(Name::anonymous(), index as u64))
                .unwrap();
        }
        let saved = active.clone();
        assert!(Arc::ptr_eq(&saved.activations, &active.activations));
        assert_eq!(
            active.activate(&env, &Name::from_components(["overflow"])),
            Err(InstanceRegistryError::Limit)
        );
        assert_eq!(active, saved);
        // Reopening an existing namespace at the limit is not a new effect.
        active
            .activate(&env, &Name::num(Name::anonymous(), 0))
            .unwrap();
        assert_eq!(active, saved);
    }

    #[test]
    fn aggregate_namespace_bytes_bind_independently_of_activation_count() {
        let env = Environment::new();
        let mut active = ActiveScopes::default();
        let text = "x".repeat(60_000);
        for index in 0..17 {
            active
                .activate(
                    &env,
                    &Name::str(Name::anonymous(), format!("{text}{index}")),
                )
                .unwrap();
        }
        let saved = active.clone();
        assert_eq!(
            active.activate(&env, &Name::str(Name::anonymous(), format!("{text}18"))),
            Err(InstanceRegistryError::Limit)
        );
        assert_eq!(active, saved);
        active
            .activate(&env, &Name::from_components(["small"]))
            .unwrap();
        assert!(active.is_active(&Name::from_components(["small"])));
        assert!(!saved.is_active(&Name::from_components(["small"])));
    }
}
