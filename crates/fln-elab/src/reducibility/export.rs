//! The pin's module-local `reducibilityCore` and imported `reducibilityExtra`.
//!
//! Exporting metadata grants no declaration authority. This reads only the
//! exact new suffix of the checked module's journal. Imported overrides retain
//! their chronological order in the extra extension; owned statuses form a map.
use super::*;
use std::collections::BTreeMap;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Registration {
    pub declaration: Name,
    pub status: Reducibility,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Statuses {
    pub owned: Vec<Registration>,
    pub imported: Vec<Registration>,
    /// Owned defaults have no wire row but must suppress native-instance
    /// fallback when the artifact's explicit statuses are assembled.
    pub default_semireducible: Vec<Name>,
    pub work: usize,
}

pub fn supports(descriptor_: &ExtensionDescriptor) -> bool {
    *descriptor_ == descriptor()
}

pub fn journal_name() -> Name {
    extension_name()
}

/// Split the exact new suffix between owned statuses and imported overrides.
/// Encoding an imported override as a local `reducibilityCore` row would lose
/// the extra map's precedence over the declaration's owning module.
/// Work meters every new payload byte before decoding or retaining its name.
pub fn statuses(
    base: &Environment,
    result: &Environment,
    max_work: usize,
) -> Result<Statuses, ReducibilityError> {
    let Some(current) = result.extension(&extension_name()) else {
        return if base.extension(&extension_name()).is_some() {
            Err(ReducibilityError::Malformed)
        } else {
            Ok(Statuses::default())
        };
    };
    if current.descriptor != descriptor() {
        return Err(ReducibilityError::Malformed);
    }
    if current.len() > MAX_ROWS {
        return Err(ReducibilityError::Limit);
    }
    let prior = base.extension(&extension_name());
    let start = prior.map_or(0, |state| state.len());
    let mut remaining = max_work;
    let mut entries = result.metadata_validation_entries(&current.descriptor.name);
    if let Some(prior) = prior {
        if prior.descriptor != current.descriptor || start > current.len() {
            return Err(ReducibilityError::Malformed);
        }
        if std::ptr::eq(prior, current) {
            return Ok(Statuses::default());
        }
        for old in prior.entries() {
            charge(&mut remaining, 1)?;
            let (new, _) = entries.next().ok_or(ReducibilityError::Malformed)?;
            // Untouched persistent entries share their payload allocation.
            // As in source-module replay, don't charge imported bytes again.
            if Arc::ptr_eq(&old.payload, &new.payload) {
                continue;
            }
            charge(&mut remaining, old.payload.len())?;
            charge(&mut remaining, new.payload.len())?;
            if old != new {
                return Err(ReducibilityError::Malformed);
            }
        }
    }
    let mut rows = BTreeMap::new();
    let mut imported = Vec::new();
    let mut defaults = BTreeSet::new();
    for (entry, validation) in entries {
        charge(&mut remaining, 1)?;
        charge(&mut remaining, entry.payload.len())?;
        let (declaration, status) = read_entry(&entry.payload)?;
        if declaration.is_anonymous() {
            return Err(ReducibilityError::Malformed);
        }
        if !validation.contains(&declaration) {
            return Err(ReducibilityError::UnknownDeclaration(declaration));
        }
        // A checked public module can retain metadata for its private
        // projections/defaults. Validate the exact anchored row against its
        // complete checked world, but only visible declaration owners receive
        // public wire rows. An unanchored missing target still refuses above.
        if !result.contains(&declaration) {
            continue;
        }
        let Some(status) = status else {
            if !base.contains(&declaration) {
                defaults.insert(declaration);
            }
            continue;
        };
        if base.contains(&declaration) {
            // ScopedEnvExtension exports newEntries in chronological order.
            // Repeated imported updates are valid and their final one wins.
            imported.push(Registration {
                declaration,
                status,
            });
        } else {
            // reducibilityCoreExt.addEntryFn uses NameMap.insert: last wins.
            rows.insert(declaration, status);
        }
    }
    let default_semireducible = defaults
        .into_iter()
        .filter(|name| !rows.contains_key(name))
        .collect();
    Ok(Statuses {
        owned: rows
            .into_iter()
            .map(|(declaration, status)| Registration {
                declaration,
                status,
            })
            .collect(),
        imported,
        default_semireducible,
        work: max_work - remaining,
    })
}

fn charge(remaining: &mut usize, count: usize) -> Result<(), ReducibilityError> {
    *remaining = remaining
        .checked_sub(count)
        .ok_or(ReducibilityError::Limit)?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use fln_core::expr::Expr;
    use fln_core::level::Level;
    use fln_core::options::KVMap;
    use fln_env::constants::{AxiomVal, ConstantInfo, ConstantVal};

    fn n(text: &str) -> Name {
        Name::from_components(text.split('.'))
    }

    fn with_axiom(env: &Environment, name: &str) -> Environment {
        env.add_decl(ConstantInfo::Axiom(AxiomVal {
            base: ConstantVal {
                name: n(name),
                level_params: Vec::new(),
                type_: Expr::sort(Level::one()),
            },
            is_unsafe: false,
        }))
        .unwrap()
    }

    #[test]
    fn only_the_owned_suffix_is_exported_with_last_status_winning() {
        let base = register(
            &with_axiom(&Environment::new(), "Imported"),
            &n("Imported"),
            Reducibility::Irreducible,
        )
        .unwrap();
        let result = with_axiom(&with_axiom(&base, "Local.a"), "Local.b");
        let result = register(&result, &n("Local.a"), Reducibility::Reducible).unwrap();
        let result = register(&result, &n("Local.b"), Reducibility::ImplicitReducible).unwrap();
        let result = register(&result, &n("Local.a"), Reducibility::Irreducible).unwrap();
        let root = result.logical_root(&KVMap::new());
        let exported = statuses(&base, &result, usize::MAX).unwrap();
        let work = exported.work;
        assert_eq!(
            exported.owned,
            [
                Registration {
                    declaration: n("Local.a"),
                    status: Reducibility::Irreducible,
                },
                Registration {
                    declaration: n("Local.b"),
                    status: Reducibility::ImplicitReducible,
                },
            ]
        );
        assert!(exported.imported.is_empty());
        assert!(work > 0);
        assert_eq!(statuses(&base, &result, work).unwrap(), exported);
        assert_eq!(
            statuses(&base, &result, work - 1),
            Err(ReducibilityError::Limit)
        );
        assert_eq!(statuses(&base, &base, 0).unwrap(), Statuses::default());
        assert_eq!(result.logical_root(&KVMap::new()), root);
    }

    #[test]
    fn private_statuses_require_exact_checked_metadata_and_do_not_become_public_rows() {
        let base = Environment::new();
        let complete = with_axiom(&with_axiom(&base, "Hidden"), "Visible");
        let complete = register(&complete, &n("Hidden"), Reducibility::Reducible).unwrap();
        let complete = register(&complete, &n("Visible"), Reducibility::Irreducible).unwrap();
        let mut public = with_axiom(&base, "Visible")
            .register_extension(descriptor())
            .unwrap();
        for entry in complete.extension(&extension_name()).unwrap().entries() {
            public = public
                .push_extension_entry(&extension_name(), Arc::clone(&entry.payload))
                .unwrap();
        }
        assert_eq!(
            statuses(&base, &public, usize::MAX),
            Err(ReducibilityError::UnknownDeclaration(n("Hidden")))
        );
        let public = public.with_imported_metadata_validation(&complete);
        let exported = statuses(&base, &public, usize::MAX).unwrap();
        assert_eq!(
            exported.owned,
            [Registration {
                declaration: n("Visible"),
                status: Reducibility::Irreducible,
            }]
        );
        assert!(exported.imported.is_empty());
        assert_eq!(statuses(&base, &public, exported.work).unwrap(), exported);
        assert_eq!(
            statuses(&base, &public, exported.work - 1),
            Err(ReducibilityError::Limit)
        );
        // A copied row appended after the bound prefix has no authority from
        // the earlier private declaration, even with identical payload bytes.
        let hidden = complete
            .extension(&extension_name())
            .unwrap()
            .entries()
            .next()
            .unwrap();
        let changed = public
            .push_extension_entry(&extension_name(), Arc::clone(&hidden.payload))
            .unwrap();
        assert_eq!(
            statuses(&base, &changed, usize::MAX),
            Err(ReducibilityError::UnknownDeclaration(n("Hidden")))
        );
    }

    #[test]
    fn a_shared_prefix_visit_is_charged_without_rereading_payload_bytes() {
        let base = register(
            &with_axiom(&Environment::new(), "Imported"),
            &n("Imported"),
            Reducibility::Irreducible,
        )
        .unwrap();
        let result = register(
            &with_axiom(&base, "Local"),
            &n("Local"),
            Reducibility::Reducible,
        )
        .unwrap();
        let suffix_cost = 1 + result
            .extension(&extension_name())
            .unwrap()
            .entries()
            .last()
            .unwrap()
            .payload
            .len();
        assert_eq!(
            statuses(&base, &result, suffix_cost),
            Err(ReducibilityError::Limit)
        );
        let exported = statuses(&base, &result, suffix_cost + 1).unwrap();
        assert_eq!(exported.owned.len(), 1);
        assert_eq!(exported.work, suffix_cost + 1);
        assert_eq!(statuses(&base, &base, 0).unwrap(), Statuses::default());
    }

    #[test]
    fn defaults_omit_wire_rows_without_dropping_explicit_semireducible_overrides() {
        let base = with_axiom(&Environment::new(), "Imported");
        let base = register(&base, &n("Imported"), Reducibility::Irreducible).unwrap();
        let result = with_axiom(&with_axiom(&base, "Default"), "Explicit");
        let result = register_default(&result, &n("Default")).unwrap();
        let result = register_default(&result, &n("Explicit")).unwrap();
        let result = register(&result, &n("Explicit"), Reducibility::Semireducible).unwrap();
        let result = register_default(&result, &n("Explicit")).unwrap();
        let result = register_default(&result, &n("Imported")).unwrap();
        let result = register(&result, &n("Imported"), Reducibility::Semireducible).unwrap();
        let exported = statuses(&base, &result, usize::MAX).unwrap();
        assert_eq!(exported.default_semireducible, [n("Default")]);
        assert_eq!(
            exported.owned,
            [Registration {
                declaration: n("Explicit"),
                status: Reducibility::Semireducible,
            }]
        );
        assert_eq!(
            exported.imported,
            [Registration {
                declaration: n("Imported"),
                status: Reducibility::Semireducible,
            }]
        );
        assert_eq!(statuses(&base, &result, exported.work).unwrap(), exported);
        assert_eq!(
            statuses(&base, &result, exported.work - 1),
            Err(ReducibilityError::Limit)
        );
    }

    #[test]
    fn imported_overrides_keep_order_without_reexporting_the_imported_prefix() {
        let base = with_axiom(&Environment::new(), "Imported");
        let base = register(&base, &n("Imported"), Reducibility::Irreducible).unwrap();
        let result = register(&base, &n("Imported"), Reducibility::Reducible).unwrap();
        let result = register(&result, &n("Imported"), Reducibility::Semireducible).unwrap();
        let result = register(
            &with_axiom(&result, "Local"),
            &n("Local"),
            Reducibility::ImplicitReducible,
        )
        .unwrap();
        let exported = statuses(&base, &result, usize::MAX).unwrap();
        assert_eq!(
            exported.imported,
            [
                Registration {
                    declaration: n("Imported"),
                    status: Reducibility::Reducible,
                },
                Registration {
                    declaration: n("Imported"),
                    status: Reducibility::Semireducible,
                },
            ]
        );
        assert_eq!(exported.owned[0].declaration, n("Local"));
        assert_eq!(statuses(&base, &result, exported.work).unwrap(), exported);
        assert_eq!(
            statuses(&base, &result, exported.work - 1),
            Err(ReducibilityError::Limit)
        );
    }

    #[test]
    fn malformed_unknown_and_rewritten_entries_are_refused() {
        let env = with_axiom(&Environment::new(), "Local");
        let base = register(&env, &n("Local"), Reducibility::Reducible).unwrap();
        let rewritten = register(&env, &n("Local"), Reducibility::Irreducible).unwrap();
        assert_eq!(
            statuses(&base, &rewritten, usize::MAX),
            Err(ReducibilityError::Malformed)
        );
        assert_eq!(
            statuses(&base, &env, usize::MAX),
            Err(ReducibilityError::Malformed)
        );
        let mut missing = MAGIC.to_vec();
        write_name(&n("Missing"), &mut missing).unwrap();
        missing.push(0);
        for payload in [Vec::new(), missing] {
            let malformed = env
                .register_extension(descriptor())
                .unwrap()
                .push_extension_entry(&extension_name(), payload)
                .unwrap();
            assert!(statuses(&Environment::new(), &malformed, usize::MAX).is_err());
        }
        let mut foreign = descriptor();
        foreign.provenance = PayloadProvenance::Opaque;
        let foreign = env.register_extension(foreign).unwrap();
        assert_eq!(
            statuses(&Environment::new(), &foreign, usize::MAX),
            Err(ReducibilityError::Malformed)
        );
    }
}
