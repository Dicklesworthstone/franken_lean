//! Lexical activation of namespace and local instances over the registration journal.
//!
//! The journal stores registrations; an `ActiveScopes` value stores *when* each
//! namespace was opened or local instance was declared. The view interleaves those events, so a
//! later global instance can outrank an earlier activation at equal priority.
//! Nothing is inserted into the environment by opening a namespace.
use super::*;
use fln_env::extensions::ExtensionState;
use std::sync::Arc;

const MAX_SCOPES: usize = 4096;
const MAX_SCOPE_BYTES: usize = 1024 * 1024;

/// Registration effects and lexical effects share the journal's clock. A local
/// effect at a boundary precedes the persistent row at that boundary.
type SelectionClock = (usize, u8, usize);

/// The last registration controls priority and clears erasure, independently of
/// the first insertion's position in the discrimination tree.
fn record_registration(
    selected: &mut BTreeMap<Name, (SelectionClock, u32)>,
    declaration: &Name,
    at: SelectionClock,
    priority: u32,
) {
    selected
        .entry(declaration.clone())
        .and_modify(|current| {
            if at > current.0 {
                *current = (at, priority);
            }
        })
        .or_insert((at, priority));
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Activation {
    kind: ActivationKind,
    at: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum ActivationKind {
    Namespace(Name),
    Local {
        class: Name,
        declaration: Name,
        priority: u32,
        index: Option<Arc<export::DerivedIndex>>,
    },
    /// A state-only removal, as at the pin's `instanceExtension.modifyState`.
    /// It is never appended to the environment's export journal.
    Erase(Name),
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
        self.activations.iter().any(
            |entry| matches!(&entry.kind, ActivationKind::Namespace(name) if name == namespace),
        )
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
        self.push(
            env,
            ActivationKind::Namespace(namespace.clone()),
            encoded.len(),
        )
    }

    /// Select an already checked local instance until this lexical snapshot is
    /// restored. The declaration and its reducibility status remain in `env`;
    /// no registration row is written to the persistent export journal.
    /// Re-registering an existing instance replaces its priority in this scope
    /// and clears an erasure, without changing its original tie position.
    pub fn register_local(
        &mut self,
        env: &Environment,
        declaration: &Name,
        priority: u32,
    ) -> Result<(), InstanceRegistryError> {
        self.validate_prefix(env)?;
        let registry = InstanceRegistry::read(env)?;
        let class = validate_instance(env, declaration)?;
        if !registry.is_class(&class) {
            return Err(InstanceRegistryError::UnknownClass(class));
        }
        let index = export::derive_local_index(env, &registry, declaration, &mut 1_000_000)?;
        // The pin keeps an older tree path when the same declaration is
        // registered under a different one. This single-slot lexical model
        // can replace priority only after proving that the path and schedule
        // are unchanged, including for imported or erased registrations.
        if let Some(previous) = registry.imported.instances.get(declaration) {
            if index.as_ref().is_none_or(|index| {
                index.keys != previous.keys || index.synth_order != previous.synth_order
            }) {
                return Err(InstanceRegistryError::InvalidInstance(declaration.clone()));
            }
        } else if registry.updates.contains_key(declaration) {
            let previous = export::derive_index(env, &registry, declaration, &mut 1_000_000)?;
            if !matches!((&previous, &index), (Some(previous), Some(index)) if previous == index) {
                return Err(InstanceRegistryError::InvalidInstance(declaration.clone()));
            }
        }
        for activation in self.activations.iter() {
            if let ActivationKind::Local {
                declaration: previous_name,
                index: previous,
                ..
            } = &activation.kind
                && previous_name == declaration
                && !matches!((previous.as_deref(), index.as_ref()),
                    (Some(previous), Some(index)) if previous == index)
            {
                return Err(InstanceRegistryError::InvalidInstance(declaration.clone()));
            }
        }
        // The pin's addLocalEntry inserts or replaces in the current scoped
        // state, even for an imported, scoped, or previously local instance.
        // This is a lexical override, not a duplicate persistent registration.
        // apply_scopes separates its new priority from the original tree slot.
        let mut encoded = Vec::new();
        write_name(&class, &mut encoded)?;
        write_name(declaration, &mut encoded)?;
        let mut bytes = encoded.len();
        if let Some(index) = &index {
            let mut keys = Vec::new();
            discr_tree::write_keys(&index.keys, &mut keys)?;
            bytes = bytes
                .checked_add(keys.len())
                .and_then(|bytes| bytes.checked_add(index.synth_order.len().checked_mul(4)?))
                .ok_or(InstanceRegistryError::Limit)?;
        }
        self.push(
            env,
            ActivationKind::Local {
                class,
                declaration: declaration.clone(),
                priority,
                index: index.map(Arc::new),
            },
            bytes,
        )
    }

    /// Remove an active instance until this lexical snapshot is restored.
    ///
    /// Like the Reference's `Instances.erase`, this fails for a declaration
    /// without an active instance attribute. The registration journal, the
    /// declaration, and its reducibility metadata are unchanged. Re-registering
    /// the same name later clears its erasure; merely reopening an already
    /// active namespace does not. No failed validation or limit check publishes
    /// a partial state.
    pub fn erase(
        &mut self,
        env: &Environment,
        declaration: &Name,
    ) -> Result<(), InstanceRegistryError> {
        self.validate_prefix(env)?;
        let registry = InstanceRegistry::read_with_scopes(env, self)?;
        if !env.contains(declaration) {
            return Err(InstanceRegistryError::UnknownDeclaration(
                declaration.clone(),
            ));
        }
        if !registry.is_instance(declaration) {
            return Err(InstanceRegistryError::NotAnInstance(declaration.clone()));
        }
        let mut encoded = Vec::new();
        write_name(declaration, &mut encoded)?;
        self.push(
            env,
            ActivationKind::Erase(declaration.clone()),
            encoded.len(),
        )
    }

    fn push(
        &mut self,
        env: &Environment,
        kind: ActivationKind,
        name_bytes: usize,
    ) -> Result<(), InstanceRegistryError> {
        let bytes = self
            .name_bytes
            .checked_add(name_bytes)
            .filter(|n| *n <= MAX_SCOPE_BYTES)
            .ok_or(InstanceRegistryError::Limit)?;
        if self.activations.len() >= MAX_SCOPES {
            return Err(InstanceRegistryError::Limit);
        }
        let anchor = env.extension(&extension_name()).cloned();
        let at = anchor.as_ref().map_or(0, ExtensionState::len);
        Arc::make_mut(&mut self.activations).push(Activation { kind, at });
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
        Self::apply_scopes(Self::read(env)?, env, scopes)
    }

    /// Derive a lexical view from the cache's validated dormant registry. The
    /// cache binds that registry to this exact environment; a scope change need
    /// not decode and validate every imported instance row a second time.
    pub(super) fn read_cached_with_scopes(
        cache: &RegistryCache,
        env: &Environment,
        scopes: &ActiveScopes,
    ) -> Result<Arc<Self>, InstanceRegistryError> {
        // Keep the fresh read's refusal order, including for a cached base.
        scopes.validate_prefix(env)?;
        let registry = cache.read(env)?;
        if scopes.activations.is_empty() {
            return Ok(registry);
        }
        Self::apply_scopes(registry.as_ref().clone(), env, scopes).map(Arc::new)
    }

    fn apply_scopes(
        mut registry: Self,
        env: &Environment,
        scopes: &ActiveScopes,
    ) -> Result<Self, InstanceRegistryError> {
        if scopes.activations.is_empty() {
            return Ok(registry);
        }
        // Clone preserves an already published index, but that index describes
        // the dormant candidate set. The activated view must derive its own,
        // within its caller's budget, without changing the dormant cache.
        registry.index = discr_tree::IndexCell::default();
        // Event keys are (journal boundary, before/at row, activation-local
        // registration order). One first activation per namespace is retained.
        let mut events = Vec::new();
        // Availability has a separate clock from candidate preference. The pin
        // updates an existing tree entry in place, preserving its search order,
        // but addInstanceEntry still clears the name from the erased set.
        let mut selected = BTreeMap::new();
        let mut erased: BTreeMap<Name, SelectionClock> = BTreeMap::new();
        let mut local_indices: BTreeMap<Name, (SelectionClock, Arc<export::DerivedIndex>)> =
            BTreeMap::new();
        for (class, rows) in &registry.instances {
            for row in rows {
                let updated = registry
                    .updates
                    .get(&row.declaration)
                    .map_or(row.order, |(at, _)| *at);
                record_registration(
                    &mut selected,
                    &row.declaration,
                    (updated, 1, 0),
                    row.priority,
                );
                events.push(((row.order, 1u8, 0usize), class.clone(), row.clone()));
            }
        }
        for (activation_index, activation) in scopes.activations.iter().enumerate() {
            let namespace = match &activation.kind {
                ActivationKind::Erase(declaration) => {
                    erased.insert(declaration.clone(), (activation.at, 0, activation_index));
                    continue;
                }
                ActivationKind::Namespace(namespace) => namespace,
                ActivationKind::Local {
                    class,
                    declaration,
                    priority,
                    index,
                } => {
                    if validate_instance(env, declaration)? != *class || !registry.is_class(class) {
                        return Err(InstanceRegistryError::Malformed);
                    }
                    if let Some(index) = index {
                        if local_indices
                            .get(declaration)
                            .is_some_and(|(_, previous)| previous.as_ref() != index.as_ref())
                        {
                            // A different path would leave multiple tree entries
                            // at the pin. This single-slot model must not guess
                            // their priority or traversal order.
                            return Err(InstanceRegistryError::InvalidInstance(
                                declaration.clone(),
                            ));
                        }
                        local_indices.insert(
                            declaration.clone(),
                            ((activation.at, 0, activation_index), Arc::clone(index)),
                        );
                    }
                    record_registration(
                        &mut selected,
                        declaration,
                        (activation.at, 0, activation_index),
                        *priority,
                    );
                    events.push((
                        (activation.at, 0u8, activation_index * (MAX_ROWS + 1)),
                        class.clone(),
                        InstanceEntry {
                            declaration: declaration.clone(),
                            priority: *priority,
                            order: 0,
                        },
                    ));
                    continue;
                }
            };
            let Some(classes) = registry.scoped.get(namespace) else {
                continue;
            };
            for (class, rows) in classes {
                for row in rows {
                    let updated = registry
                        .updates
                        .get(&row.declaration)
                        .map_or(row.order, |(at, _)| *at);
                    let effect = (updated, 1, 0).max((activation.at, 0, activation_index));
                    record_registration(&mut selected, &row.declaration, effect, row.priority);
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
        // The pin's DiscrTree.insertVal replaces an existing value in place:
        // promoting a local registration must not make it a newer peer. Keep
        // the first insertion slot and use the last effect's priority. Erasure
        // also leaves the tree slot intact, so restoration follows the same law.
        let mut seen = BTreeSet::new();
        registry.instances.clear();
        for (order, (_, class, mut row)) in events.into_iter().enumerate() {
            if !seen.insert(row.declaration.clone()) {
                continue;
            }
            let (added, priority) = selected
                .get(&row.declaration)
                .ok_or(InstanceRegistryError::Malformed)?;
            row.order = order;
            row.priority = *priority;
            if erased
                .get(&row.declaration)
                .is_some_and(|removed| removed > added)
            {
                // Dormant scoped rows remain in `registry.scoped`; retaining
                // them again would duplicate `native_instances` metadata.
                if !registry
                    .updates
                    .get(&row.declaration)
                    .is_some_and(|(_, scope)| scope.is_some())
                {
                    registry.inactive.push(row);
                }
                continue;
            }
            if let Some((captured_at, index)) = local_indices.get(&row.declaration) {
                if captured_at != added {
                    // A later global/scoped registration may replace the local
                    // selection. An imported entry keeps its saved index when a
                    // namespace opens; otherwise require the same immutable path.
                    // Never replace an alias's captured path with broad search.
                    let same =
                        if let Some(previous) = registry.imported.instances.get(&row.declaration) {
                            previous.keys == index.keys && previous.synth_order == index.synth_order
                        } else {
                            export::derive_index(env, &registry, &row.declaration, &mut 1_000_000)?
                                .as_ref()
                                == Some(index.as_ref())
                        };
                    if !same {
                        return Err(InstanceRegistryError::InvalidInstance(row.declaration));
                    }
                }
                registry
                    .local_indices
                    .insert(row.declaration.clone(), Arc::clone(index));
            }
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

    fn cache_fixture(with_global: bool) -> Environment {
        use fln_core::level::Level;
        use fln_env::constants::{AxiomVal, ConstantVal};

        let class = Name::from_components(["C"]);
        let axiom = |name: &str, type_: Expr| {
            ConstantInfo::Axiom(AxiomVal {
                base: ConstantVal {
                    name: Name::from_components([name]),
                    level_params: Vec::new(),
                    type_,
                },
                is_unsafe: false,
            })
        };
        let mut env = Environment::new()
            .add_decl(axiom("C", Expr::sort(Level::one())))
            .unwrap();
        for name in ["global", "scoped", "local", "later"] {
            env = env
                .add_decl(axiom(name, Expr::const_(class.clone(), Vec::new())))
                .unwrap();
        }
        env = register_class(&env, &class).unwrap();
        if with_global {
            env = register_instance(&env, &Name::from_components(["global"]), 1000).unwrap();
        }
        register(
            &env,
            &Name::from_components(["N"]),
            &Name::from_components(["scoped"]),
            1000,
        )
        .unwrap()
    }

    fn candidate_names(registry: &InstanceRegistry) -> Vec<Name> {
        registry
            .candidates(&Name::from_components(["C"]))
            .iter()
            .map(|row| row.declaration.clone())
            .collect()
    }

    #[test]
    fn cached_empty_scopes_share_the_dormant_registry_in_both_read_orders() {
        let env = cache_fixture(true);
        let scopes = ActiveScopes::default();
        for scoped_first in [false, true] {
            let cache = RegistryCache::default();
            let first = if scoped_first {
                cache.read_with_scopes(&env, &scopes).unwrap()
            } else {
                cache.read(&env).unwrap()
            };
            assert!(Arc::ptr_eq(&first, &cache.read(&env).unwrap()));
            assert!(Arc::ptr_eq(
                &first,
                &cache.read_with_scopes(&env, &scopes).unwrap()
            ));
            assert_eq!(*first, InstanceRegistry::read(&env).unwrap());
        }
    }

    #[test]
    fn cached_scope_views_preserve_activation_order_local_priority_and_promotion() {
        let env = cache_fixture(true);
        let cache = RegistryCache::default();
        let dormant = cache.read(&env).unwrap();
        let mut opened = ActiveScopes::default();
        opened
            .activate(&env, &Name::from_components(["N"]))
            .unwrap();
        let opened_view = cache.read_with_scopes(&env, &opened).unwrap();
        assert_eq!(
            candidate_names(&opened_view),
            ["scoped", "global"].map(|name| Name::from_components([name]))
        );
        assert_eq!(
            *opened_view,
            InstanceRegistry::read_with_scopes(&env, &opened).unwrap()
        );
        let mut local = opened.clone();
        local
            .register_local(&env, &Name::from_components(["local"]), 2000)
            .unwrap();
        let local_view = cache.read_with_scopes(&env, &local).unwrap();
        assert_eq!(
            candidate_names(&local_view),
            ["local", "scoped", "global"].map(|name| Name::from_components([name]))
        );
        assert_eq!(
            *local_view,
            InstanceRegistry::read_with_scopes(&env, &local).unwrap()
        );
        assert!(Arc::ptr_eq(&dormant, &cache.read(&env).unwrap()));
        assert_eq!(
            candidate_names(&dormant),
            [Name::from_components(["global"])]
        );
        // Returning to an earlier lexical snapshot never leaks local instances.
        assert_eq!(
            *cache.read_with_scopes(&env, &opened).unwrap(),
            *opened_view
        );

        let later = register_instance(&env, &Name::from_components(["later"]), 1000).unwrap();
        let later_view = cache.read_with_scopes(&later, &local).unwrap();
        assert_eq!(
            candidate_names(&later_view),
            ["local", "later", "scoped", "global"].map(|name| Name::from_components([name]))
        );
        assert_eq!(
            *later_view,
            InstanceRegistry::read_with_scopes(&later, &local).unwrap()
        );
        // A global registration supersedes the local event, including priority.
        let promoted = set_instance(&later, &Name::from_components(["local"]), 500).unwrap();
        let promoted_view = cache.read_with_scopes(&promoted, &local).unwrap();
        assert_eq!(
            candidate_names(&promoted_view),
            ["later", "scoped", "global", "local"].map(|name| Name::from_components([name]))
        );
        assert_eq!(
            *promoted_view,
            InstanceRegistry::read_with_scopes(&promoted, &local).unwrap()
        );
    }

    #[test]
    fn activated_views_do_not_inherit_a_warm_dormant_index_or_skip_its_budget() {
        let env = cache_fixture(false);
        let cache = RegistryCache::default();
        let dormant = cache.read(&env).unwrap();
        assert!(candidate_names(&dormant).is_empty());
        // With no global candidates, an empty index is complete with zero work.
        let mut no_work = 0;
        let dormant_index = dormant.instance_index(&env, &mut no_work).unwrap();
        let mut opened = ActiveScopes::default();
        opened
            .activate(&env, &Name::from_components(["N"]))
            .unwrap();
        let active = cache.read_with_scopes(&env, &opened).unwrap();
        assert_eq!(
            candidate_names(&active),
            [Name::from_components(["scoped"])]
        );
        for _ in 0..2 {
            // A cloned warm index would incorrectly succeed here, bypassing
            // both the newly active row and the caller's zero-work budget.
            assert!(matches!(
                active.instance_index(&env, &mut no_work),
                Err(InstanceRegistryError::Limit)
            ));
        }
        assert!(std::ptr::eq(
            dormant_index,
            dormant.instance_index(&env, &mut no_work).unwrap()
        ));
        assert!(Arc::ptr_eq(&dormant, &cache.read(&env).unwrap()));
    }

    #[test]
    fn cached_scope_failures_preserve_prefix_and_local_declaration_validation() {
        use fln_env::constants::{AxiomVal, ConstantVal};

        let base = cache_fixture(true);
        let temporary = Name::from_components(["temporary"]);
        let env = base
            .add_decl(ConstantInfo::Axiom(AxiomVal {
                base: ConstantVal {
                    name: temporary.clone(),
                    level_params: Vec::new(),
                    type_: Expr::const_(Name::from_components(["C"]), Vec::new()),
                },
                is_unsafe: false,
            }))
            .unwrap();
        let mut scopes = ActiveScopes::default();
        scopes.register_local(&env, &temporary, 2000).unwrap();
        let cache = RegistryCache::default();
        let valid = cache.read_with_scopes(&env, &scopes).unwrap();
        for _ in 0..2 {
            // The journal prefix agrees but the local declaration was rolled back.
            assert_eq!(
                cache.read_with_scopes(&base, &scopes),
                Err(InstanceRegistryError::UnknownDeclaration(temporary.clone()))
            );
            // A missing anchor is refused before any base view can be reused.
            assert_eq!(
                cache.read_with_scopes(&Environment::new(), &scopes),
                Err(InstanceRegistryError::Malformed)
            );
            assert!(Arc::ptr_eq(
                &valid,
                &cache.read_with_scopes(&env, &scopes).unwrap()
            ));
        }
    }

    #[test]
    fn erasure_changes_selection_without_changing_registration_or_reducibility() {
        let env = cache_fixture(true);
        let saved_env = env.clone();
        let global = Name::from_components(["global"]);
        let mut scopes = ActiveScopes::default();
        let saved_scope = scopes.clone();
        let before = InstanceRegistry::read_with_scopes(&env, &scopes).unwrap();
        let names_before: BTreeSet<_> = before.native_instances().cloned().collect();
        assert!(before.is_instance(&global));

        scopes.erase(&env, &global).unwrap();
        let after = InstanceRegistry::read_with_scopes(&env, &scopes).unwrap();
        assert!(!after.is_instance(&global));
        assert!(candidate_names(&after).is_empty());
        assert_eq!(env, saved_env, "erasure writes no persistent metadata");
        assert_eq!(
            after.native_instances().cloned().collect::<BTreeSet<_>>(),
            names_before
        );
        assert_eq!(
            after.native_instances().count(),
            names_before.len(),
            "no metadata duplicates"
        );
        assert!(
            InstanceRegistry::read(&env).unwrap().is_instance(&global),
            "the exported registration survives"
        );
        assert!(
            InstanceRegistry::read_with_scopes(&env, &saved_scope)
                .unwrap()
                .is_instance(&global),
            "restoring a scope restores selection"
        );
    }

    #[test]
    fn only_an_active_instance_can_be_erased_and_failures_are_atomic() {
        let env = cache_fixture(true);
        let mut scopes = ActiveScopes::default();
        for (name, error) in [
            (
                "missing",
                InstanceRegistryError::UnknownDeclaration(Name::from_components(["missing"])),
            ),
            (
                "local",
                InstanceRegistryError::NotAnInstance(Name::from_components(["local"])),
            ),
            (
                "scoped",
                InstanceRegistryError::NotAnInstance(Name::from_components(["scoped"])),
            ),
        ] {
            let saved = scopes.clone();
            assert_eq!(
                scopes.erase(&env, &Name::from_components([name])),
                Err(error)
            );
            assert_eq!(scopes, saved);
        }
        let global = Name::from_components(["global"]);
        scopes.erase(&env, &global).unwrap();
        let saved = scopes.clone();
        let error = scopes.erase(&env, &global).unwrap_err();
        assert_eq!(error, InstanceRegistryError::NotAnInstance(global));
        assert_eq!(
            error.to_string(),
            "`global` does not have [instance] attribute"
        );
        assert_eq!(scopes, saved);
    }

    #[test]
    fn global_reregistration_clears_erasure_without_moving_equal_priority_order() {
        let global = Name::from_components(["global"]);
        let env = register_instance(
            &cache_fixture(true),
            &Name::from_components(["later"]),
            1000,
        )
        .unwrap();
        let mut scopes = ActiveScopes::default();
        scopes.erase(&env, &global).unwrap();
        assert_eq!(
            candidate_names(&InstanceRegistry::read_with_scopes(&env, &scopes).unwrap()),
            [Name::from_components(["later"])]
        );

        // set_instance updates the original slot, but addInstanceEntry clears
        // erasure even when neither priority nor preference position changes.
        let restored = set_instance(&env, &global, 1000).unwrap();
        assert_eq!(
            candidate_names(&InstanceRegistry::read_with_scopes(&restored, &scopes).unwrap()),
            ["later", "global"].map(|name| Name::from_components([name]))
        );
        // A subsequent erasure wins over that update, and the next update wins
        // again: the clocks must distinguish every journal boundary.
        scopes.erase(&restored, &global).unwrap();
        let promoted = set_instance(&restored, &global, 2000).unwrap();
        assert_eq!(
            candidate_names(&InstanceRegistry::read_with_scopes(&promoted, &scopes).unwrap()),
            ["global", "later"].map(|name| Name::from_components([name]))
        );
    }

    #[test]
    fn scoped_reregistration_clears_erasure_but_reopening_does_not() {
        let env = cache_fixture(true);
        let namespace = Name::from_components(["N"]);
        let scoped = Name::from_components(["scoped"]);
        let mut scopes = ActiveScopes::default();
        scopes.activate(&env, &namespace).unwrap();
        scopes.erase(&env, &scoped).unwrap();
        let erased = scopes.clone();
        scopes.activate(&env, &namespace).unwrap();
        assert_eq!(scopes, erased, "an already open namespace adds no event");
        let hidden = InstanceRegistry::read_with_scopes(&env, &scopes).unwrap();
        assert_eq!(
            candidate_names(&hidden),
            [Name::from_components(["global"])]
        );
        assert_eq!(
            hidden
                .native_instances()
                .filter(|name| *name == &scoped)
                .count(),
            1
        );
        let restored = register(&env, &namespace, &scoped, 1000).unwrap();
        assert_eq!(
            candidate_names(&InstanceRegistry::read_with_scopes(&restored, &scopes).unwrap()),
            ["scoped", "global"].map(|name| Name::from_components([name]))
        );
    }

    #[test]
    fn erasures_interleave_with_local_activations_at_the_same_journal_boundary() {
        let env = cache_fixture(true);
        let mut scopes = ActiveScopes::default();
        scopes
            .activate(&env, &Name::from_components(["N"]))
            .unwrap();
        scopes
            .erase(&env, &Name::from_components(["scoped"]))
            .unwrap();
        scopes
            .register_local(&env, &Name::from_components(["local"]), 2000)
            .unwrap();
        let outer = scopes.clone();
        scopes
            .erase(&env, &Name::from_components(["local"]))
            .unwrap();
        let hidden = InstanceRegistry::read_with_scopes(&env, &scopes).unwrap();
        assert_eq!(
            candidate_names(&hidden),
            [Name::from_components(["global"])]
        );
        assert!(
            hidden
                .native_instances()
                .any(|name| name == &Name::from_components(["local"]))
        );
        assert_eq!(
            candidate_names(&InstanceRegistry::read_with_scopes(&env, &outer).unwrap()),
            ["local", "global"].map(|name| Name::from_components([name]))
        );
        let promoted = set_instance(&env, &Name::from_components(["local"]), 500).unwrap();
        assert_eq!(
            candidate_names(&InstanceRegistry::read_with_scopes(&promoted, &scopes).unwrap()),
            ["global", "local"].map(|name| Name::from_components([name]))
        );
    }

    #[test]
    fn erasure_is_bound_to_its_original_journal_prefix() {
        let env = cache_fixture(true);
        let mut scopes = ActiveScopes::default();
        scopes
            .erase(&env, &Name::from_components(["global"]))
            .unwrap();
        let saved = scopes.clone();
        assert_eq!(
            scopes.erase(&Environment::new(), &Name::from_components(["global"])),
            Err(InstanceRegistryError::Malformed)
        );
        assert_eq!(scopes, saved);
        assert!(matches!(
            InstanceRegistry::read_with_scopes(&Environment::new(), &scopes),
            Err(InstanceRegistryError::Malformed)
        ));
    }

    #[test]
    fn erasure_respects_the_scope_event_limit_without_losing_the_active_instance() {
        let env = cache_fixture(true);
        // Exercise the same frozen boundary as public activation without doing
        // thousands of unrelated full registry reads in this focused test.
        let mut scopes = ActiveScopes {
            activations: Arc::new(vec![
                Activation {
                    kind: ActivationKind::Namespace(Name::from_components(["unused"])),
                    at: 0,
                };
                MAX_SCOPES
            ]),
            ..ActiveScopes::default()
        };
        let saved = scopes.clone();
        assert_eq!(
            scopes.erase(&env, &Name::from_components(["global"])),
            Err(InstanceRegistryError::Limit)
        );
        assert_eq!(scopes, saved);
        assert!(
            InstanceRegistry::read_with_scopes(&env, &scopes)
                .unwrap()
                .is_instance(&Name::from_components(["global"]))
        );
    }

    #[test]
    fn cached_erasure_views_do_not_poison_the_dormant_or_restored_scope() {
        let env = cache_fixture(true);
        let cache = RegistryCache::default();
        let before = ActiveScopes::default();
        let dormant = cache.read_with_scopes(&env, &before).unwrap();
        let mut scopes = before.clone();
        scopes
            .erase(&env, &Name::from_components(["global"]))
            .unwrap();
        let erased = cache.read_with_scopes(&env, &scopes).unwrap();
        assert!(!Arc::ptr_eq(&dormant, &erased));
        assert!(candidate_names(&erased).is_empty());
        assert!(Arc::ptr_eq(
            &erased,
            &cache.read_with_scopes(&env, &scopes).unwrap()
        ));
        assert!(Arc::ptr_eq(&dormant, &cache.read(&env).unwrap()));
        assert!(Arc::ptr_eq(
            &dormant,
            &cache.read_with_scopes(&env, &before).unwrap()
        ));
    }

    #[test]
    fn promoting_a_local_instance_preserves_its_first_tie_slot() {
        let local = Name::from_components(["local"]);
        let later = Name::from_components(["later"]);
        for erase_first in [false, true] {
            let base = cache_fixture(false);
            let outer = ActiveScopes::default();
            let mut scopes = outer.clone();
            scopes.register_local(&base, &local, 1000).unwrap();
            let env = register_instance(&base, &later, 1000).unwrap();
            if erase_first {
                scopes.erase(&env, &local).unwrap();
            }
            let promoted = set_instance(&env, &local, 1000).unwrap();
            let inner = InstanceRegistry::read_with_scopes(&promoted, &scopes).unwrap();
            assert_eq!(
                candidate_names(&inner),
                [later.clone(), local.clone()],
                "replacement (including after erasure) keeps the original tree slot"
            );
            // The outer scope first sees `local` at its persistent registration,
            // so its own tree quite correctly prefers it over `later`.
            assert_eq!(
                candidate_names(&InstanceRegistry::read_with_scopes(&promoted, &outer).unwrap()),
                [local.clone(), later.clone()]
            );
            let raised = set_instance(&promoted, &local, 2000).unwrap();
            assert_eq!(
                candidate_names(&InstanceRegistry::read_with_scopes(&raised, &scopes).unwrap()),
                [local.clone(), later.clone()],
                "preserving a slot must not preserve an obsolete priority"
            );
        }
    }

    #[test]
    fn scoped_promotion_replaces_priority_without_reinserting_the_local_candidate() {
        let base = cache_fixture(false);
        let local = Name::from_components(["local"]);
        let namespace = Name::from_components(["N"]);
        let mut scopes = ActiveScopes::default();
        scopes.activate(&base, &namespace).unwrap();
        scopes.register_local(&base, &local, 3000).unwrap();
        let env = register_instance(&base, &Name::from_components(["later"]), 1000).unwrap();
        let promoted = register(&env, &namespace, &local, 1000).unwrap();
        let selected = InstanceRegistry::read_with_scopes(&promoted, &scopes).unwrap();
        assert_eq!(
            candidate_names(&selected),
            ["later", "local", "scoped"].map(|name| Name::from_components([name]))
        );
        assert_eq!(
            selected.candidates(&Name::from_components(["C"]))[1].priority,
            1000
        );
    }

    #[test]
    fn promoting_one_of_two_same_boundary_locals_does_not_reverse_them() {
        let env = cache_fixture(false);
        let first = Name::from_components(["local"]);
        let second = Name::from_components(["global"]);
        let mut scopes = ActiveScopes::default();
        scopes.register_local(&env, &first, 1000).unwrap();
        scopes.register_local(&env, &second, 1000).unwrap();
        let promoted = set_instance(&env, &first, 1000).unwrap();
        assert_eq!(
            candidate_names(&InstanceRegistry::read_with_scopes(&promoted, &scopes).unwrap()),
            [second, first]
        );
    }

    #[test]
    fn local_overrides_of_existing_globals_preserve_ties_and_restore_on_rollback() {
        let name = Name::from_components(["global"]);
        let later = Name::from_components(["later"]);
        let env = register_instance(&cache_fixture(true), &later, 1000).unwrap();
        let original = env.clone();
        let outer = ActiveScopes::default();
        let mut scopes = outer.clone();
        scopes.register_local(&env, &name, 1000).unwrap();
        assert_eq!(
            candidate_names(&InstanceRegistry::read_with_scopes(&env, &scopes).unwrap()),
            [later.clone(), name.clone()],
            "an equal-priority override replaces, rather than appends"
        );
        scopes.register_local(&env, &name, 2000).unwrap();
        let raised = scopes.clone();
        assert_eq!(
            candidate_names(&InstanceRegistry::read_with_scopes(&env, &raised).unwrap()),
            [name.clone(), later.clone()]
        );
        scopes.register_local(&env, &name, 50).unwrap();
        assert_eq!(
            candidate_names(&InstanceRegistry::read_with_scopes(&env, &scopes).unwrap()),
            [later.clone(), name.clone()],
            "the last override wins, not the greatest priority"
        );
        assert_eq!(
            candidate_names(&InstanceRegistry::read_with_scopes(&env, &raised).unwrap()),
            [name.clone(), later.clone()]
        );
        assert_eq!(
            candidate_names(&InstanceRegistry::read_with_scopes(&env, &outer).unwrap()),
            [later, name]
        );
        assert_eq!(env, original, "no local override enters the export journal");
    }

    #[test]
    fn a_local_override_can_restore_an_erased_global_or_local_instance() {
        let env = cache_fixture(true);
        for name in ["global", "local"] {
            let name = Name::from_components([name]);
            let mut scopes = ActiveScopes::default();
            if !InstanceRegistry::read(&env).unwrap().is_instance(&name) {
                scopes.register_local(&env, &name, 1000).unwrap();
            }
            for priority in [2000, 500, 1000] {
                scopes.erase(&env, &name).unwrap();
                assert!(
                    !InstanceRegistry::read_with_scopes(&env, &scopes)
                        .unwrap()
                        .is_instance(&name)
                );
                scopes.register_local(&env, &name, priority).unwrap();
                let selected = InstanceRegistry::read_with_scopes(&env, &scopes).unwrap();
                let candidates = selected.candidates(&Name::from_components(["C"]));
                let row = candidates
                    .iter()
                    .find(|row| row.declaration == name)
                    .unwrap();
                assert_eq!(row.priority, priority);
                assert_eq!(
                    candidates
                        .iter()
                        .filter(|row| row.declaration == name)
                        .count(),
                    1,
                    "restoration must not leave duplicate candidates"
                );
            }
        }
    }

    #[test]
    fn global_and_local_priority_updates_follow_effect_time_not_first_slot() {
        let name = Name::from_components(["global"]);
        let later = Name::from_components(["later"]);
        let base = register_instance(&cache_fixture(true), &later, 4000).unwrap();
        let mut scopes = ActiveScopes::default();
        scopes.register_local(&base, &name, 3000).unwrap();
        let updated = set_instance(&base, &name, 5000).unwrap();
        assert_eq!(
            candidate_names(&InstanceRegistry::read_with_scopes(&updated, &scopes).unwrap()),
            [name.clone(), later.clone()]
        );
        scopes.register_local(&updated, &name, 2000).unwrap();
        assert_eq!(
            candidate_names(&InstanceRegistry::read_with_scopes(&updated, &scopes).unwrap()),
            [later.clone(), name.clone()]
        );
        let restored = set_instance(&updated, &name, 6000).unwrap();
        assert_eq!(
            candidate_names(&InstanceRegistry::read_with_scopes(&restored, &scopes).unwrap()),
            [name, later]
        );
    }

    #[test]
    fn dormant_scoped_instances_can_be_selected_locally_without_opening_the_namespace() {
        let env = cache_fixture(true);
        let name = Name::from_components(["scoped"]);
        let namespace = Name::from_components(["N"]);
        let mut scopes = ActiveScopes::default();
        let outer = scopes.clone();
        scopes.register_local(&env, &name, 2000).unwrap();
        assert!(!scopes.is_active(&namespace));
        let view = InstanceRegistry::read_with_scopes(&env, &scopes).unwrap();
        assert_eq!(candidate_names(&view)[0], name);
        assert!(
            !InstanceRegistry::read_with_scopes(&env, &outer)
                .unwrap()
                .is_instance(&name)
        );
        // A first activation is a new registration effect. Reopening is not.
        scopes.activate(&env, &namespace).unwrap();
        let priority = |env: &Environment, scopes: &ActiveScopes| {
            InstanceRegistry::read_with_scopes(env, scopes)
                .unwrap()
                .candidates(&Name::from_components(["C"]))
                .iter()
                .find(|row| row.declaration == name)
                .unwrap()
                .priority
        };
        assert_eq!(priority(&env, &scopes), 1000);
        scopes.register_local(&env, &name, 3000).unwrap();
        scopes.activate(&env, &namespace).unwrap();
        assert_eq!(priority(&env, &scopes), 3000);
        let updated = register(&env, &namespace, &name, 4000).unwrap();
        assert_eq!(priority(&updated, &scopes), 4000);
        scopes.register_local(&updated, &name, 500).unwrap();
        assert_eq!(priority(&updated, &scopes), 500);
    }

    #[test]
    fn repeated_local_registration_keeps_its_first_same_boundary_position() {
        let env = cache_fixture(false);
        let first = Name::from_components(["local"]);
        let second = Name::from_components(["global"]);
        let mut scopes = ActiveScopes::default();
        scopes.register_local(&env, &first, 1000).unwrap();
        scopes.register_local(&env, &second, 1000).unwrap();
        scopes.register_local(&env, &first, 1000).unwrap();
        assert_eq!(
            candidate_names(&InstanceRegistry::read_with_scopes(&env, &scopes).unwrap()),
            [second, first]
        );
    }

    #[test]
    fn failed_local_overrides_preserve_the_complete_lexical_snapshot() {
        let env = cache_fixture(true);
        let name = Name::from_components(["global"]);
        let mut scopes = ActiveScopes::default();
        scopes.register_local(&env, &name, 2000).unwrap();
        let saved = scopes.clone();
        let missing = Name::from_components(["missing"]);
        assert_eq!(
            scopes.register_local(&env, &missing, 5000),
            Err(InstanceRegistryError::UnknownDeclaration(missing))
        );
        assert_eq!(scopes, saved);
        assert_eq!(
            scopes.register_local(&Environment::new(), &name, 5000),
            Err(InstanceRegistryError::Malformed)
        );
        assert_eq!(scopes, saved);
        // An override still consumes lexical history space, even when the name
        // is already registered. Failure cannot publish the replacement.
        scopes.name_bytes = MAX_SCOPE_BYTES;
        let full = scopes.clone();
        assert_eq!(
            scopes.register_local(&env, &name, 5000),
            Err(InstanceRegistryError::Limit)
        );
        assert_eq!(scopes, full);
        let selected = InstanceRegistry::read_with_scopes(&env, &scopes).unwrap();
        assert_eq!(
            selected.candidates(&Name::from_components(["C"]))[0].priority,
            2000
        );
    }

    #[test]
    fn local_override_views_never_reuse_a_warm_dormant_index() {
        let env = cache_fixture(false);
        let cache = RegistryCache::default();
        let dormant = cache.read(&env).unwrap();
        let mut zero = 0;
        let index = dormant.instance_index(&env, &mut zero).unwrap();
        let mut scopes = ActiveScopes::default();
        scopes
            .register_local(&env, &Name::from_components(["scoped"]), 2000)
            .unwrap();
        let selected = cache.read_with_scopes(&env, &scopes).unwrap();
        assert_eq!(
            *selected,
            InstanceRegistry::read_with_scopes(&env, &scopes).unwrap()
        );
        assert!(matches!(
            selected.instance_index(&env, &mut zero),
            Err(InstanceRegistryError::Limit)
        ));
        assert!(std::ptr::eq(
            index,
            dormant.instance_index(&env, &mut zero).unwrap()
        ));
        assert!(Arc::ptr_eq(&dormant, &cache.read(&env).unwrap()));
    }

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
