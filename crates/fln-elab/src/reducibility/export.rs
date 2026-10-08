//! The module-local `reducibilityCore` map written by the pinned Reference.
//!
//! Exporting metadata grants no declaration authority. This reads only the
//! exact new suffix of the checked module's journal. Changes to an imported
//! declaration require `reducibilityExtra`, which has no serializer here.
use super::*;
use std::collections::BTreeMap;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Registration {
    pub declaration: Name,
    pub status: Reducibility,
}

pub fn supports(descriptor_: &ExtensionDescriptor) -> bool {
    *descriptor_ == descriptor()
}

pub fn journal_name() -> Name {
    extension_name()
}

/// Collect this module's final status for each of its own declarations.
/// `None` refuses an imported-declaration override: encoding it as a local
/// `reducibilityCore` row would silently change the pinned import semantics.
/// Work meters every new payload byte before decoding or retaining its name.
pub fn statuses(
    base: &Environment,
    result: &Environment,
    max_work: usize,
) -> Result<Option<(Vec<Registration>, usize)>, ReducibilityError> {
    let Some(current) = result.extension(&extension_name()) else {
        return if base.extension(&extension_name()).is_some() {
            Err(ReducibilityError::Malformed)
        } else {
            Ok(Some((Vec::new(), 0)))
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
    let mut entries = current.entries();
    if let Some(prior) = prior {
        if prior.descriptor != current.descriptor || start > current.len() {
            return Err(ReducibilityError::Malformed);
        }
        if std::ptr::eq(prior, current) {
            return Ok(Some((Vec::new(), 0)));
        }
        for old in prior.entries() {
            charge(&mut remaining, 1)?;
            let new = entries.next().ok_or(ReducibilityError::Malformed)?;
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
    for entry in entries {
        charge(&mut remaining, 1)?;
        charge(&mut remaining, entry.payload.len())?;
        if entry.payload.len() > MAX_ENTRY_BYTES {
            return Err(ReducibilityError::Limit);
        }
        let mut bytes = entry
            .payload
            .strip_prefix(MAGIC)
            .ok_or(ReducibilityError::Malformed)?;
        let declaration = read_name(&mut bytes).map_err(codec)?;
        let [tag] = bytes else {
            return Err(ReducibilityError::Malformed);
        };
        let status = Reducibility::from_tag(*tag).ok_or(ReducibilityError::Malformed)?;
        if declaration.is_anonymous() {
            return Err(ReducibilityError::Malformed);
        }
        if !result.contains(&declaration) {
            return Err(ReducibilityError::UnknownDeclaration(declaration));
        }
        if base.contains(&declaration) {
            return Ok(None);
        }
        // reducibilityCoreExt.addEntryFn uses NameMap.insert: last wins.
        rows.insert(declaration, status);
    }
    Ok(Some((
        rows.into_iter()
            .map(|(declaration, status)| Registration {
                declaration,
                status,
            })
            .collect(),
        max_work - remaining,
    )))
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
        let (rows, work) = statuses(&base, &result, usize::MAX).unwrap().unwrap();
        assert_eq!(
            rows,
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
        assert!(work > 0);
        assert_eq!(statuses(&base, &result, work).unwrap(), Some((rows, work)));
        assert_eq!(
            statuses(&base, &result, work - 1),
            Err(ReducibilityError::Limit)
        );
        assert_eq!(statuses(&base, &base, 0).unwrap(), Some((Vec::new(), 0)));
        assert_eq!(result.logical_root(&KVMap::new()), root);
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
        let (rows, work) = statuses(&base, &result, suffix_cost + 1).unwrap().unwrap();
        assert_eq!(rows.len(), 1);
        assert_eq!(work, suffix_cost + 1);
        assert_eq!(statuses(&base, &base, 0).unwrap(), Some((Vec::new(), 0)));
    }

    #[test]
    fn an_imported_override_requires_the_extra_extension_serializer() {
        let base = with_axiom(&Environment::new(), "Imported");
        let result = register(&base, &n("Imported"), Reducibility::Reducible).unwrap();
        assert_eq!(statuses(&base, &result, usize::MAX).unwrap(), None);
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
