//! Module-owned `macroInline` rows for the pin's `inlineAttrs` enum map.
//!
//! The native journal contains the final macro-inline decisions after source
//! attributes have been applied in order. Imported entries retain their own
//! module identity; exporting them again would change the pin's lookup rules.
use super::*;
use std::sync::Arc;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Registrations {
    pub declarations: Vec<Name>,
    pub work: usize,
    pub bytes_examined: usize,
}

/// Read only the checked module's new journal suffix, charging before decoding.
/// `None` refuses an attribute on an imported declaration, as the pin's enum
/// attributes do. The imported prefix must be unchanged, including its order.
pub fn registrations(
    base: &Environment,
    result: &Environment,
    max_work: usize,
) -> Result<Option<Registrations>, MacroInlineError> {
    let empty = || {
        Some(Registrations {
            declarations: Vec::new(),
            work: 0,
            bytes_examined: 0,
        })
    };
    let Some(current) = result.extension(&journal_name()) else {
        return if base.extension(&journal_name()).is_some() {
            Err(MacroInlineError::Malformed)
        } else {
            Ok(empty())
        };
    };
    if !supports(&current.descriptor) {
        return Err(MacroInlineError::Malformed);
    }
    if current.len() > MAX_ROWS {
        return Err(MacroInlineError::Limit);
    }
    let mut remaining = max_work;
    let mut bytes_examined = 0;
    let mut entries = current.entries();
    if let Some(prior) = base.extension(&journal_name()) {
        if prior.descriptor != current.descriptor || prior.len() > current.len() {
            return Err(MacroInlineError::Malformed);
        }
        if std::ptr::eq(prior, current) {
            return Ok(empty());
        }
        for old in prior.entries() {
            charge(&mut remaining, 1)?;
            let new = entries.next().ok_or(MacroInlineError::Malformed)?;
            if Arc::ptr_eq(&old.payload, &new.payload) {
                continue;
            }
            for payload in [&old.payload, &new.payload] {
                charge(&mut remaining, payload.len())?;
                bytes_examined += payload.len();
            }
            if old != new {
                return Err(MacroInlineError::Malformed);
            }
        }
    }
    let mut declarations = BTreeSet::new();
    for entry in entries {
        charge(&mut remaining, 1)?;
        charge(&mut remaining, entry.payload.len())?;
        bytes_examined += entry.payload.len();
        if entry.payload.len() > MAX_ENTRY_BYTES {
            return Err(MacroInlineError::Limit);
        }
        let mut bytes = entry
            .payload
            .strip_prefix(MAGIC)
            .ok_or(MacroInlineError::Malformed)?;
        let declaration = read_name(&mut bytes).map_err(codec)?;
        if !bytes.is_empty() || declaration.is_anonymous() {
            return Err(MacroInlineError::Malformed);
        }
        eligible(result, &declaration)?;
        if base.contains(&declaration) {
            return Ok(None);
        }
        if !declarations.insert(declaration.clone()) {
            return Err(MacroInlineError::Duplicate(declaration));
        }
    }
    Ok(Some(Registrations {
        declarations: declarations.into_iter().collect(),
        work: max_work - remaining,
        bytes_examined,
    }))
}

fn charge(remaining: &mut usize, count: usize) -> Result<(), MacroInlineError> {
    *remaining = remaining
        .checked_sub(count)
        .ok_or(MacroInlineError::Limit)?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use fln_core::expr::Expr;
    use fln_core::level::Level;
    use fln_core::options::KVMap;
    use fln_core::outcome::Outcome;
    use fln_env::constants::{ConstantVal, DefinitionSafety, DefinitionVal, ReducibilityHints};
    use fln_env::environment::{DeclarationBudget, DeclarationCommitted};
    use fln_env::pmap::CollisionBudget;
    use fln_kernel::Declaration;
    use fln_kernel::capability::{Published, admit};
    use fln_kernel::council::{Council, CouncilOutcome, convene};
    use fln_kernel::verdict::Budget;

    fn n(text: &str) -> Name {
        Name::from_components(text.split('.'))
    }

    // Kernel-checked codec fixtures. Artifact integration tests additionally
    // use the checked source pipeline and the independent admission seat.
    fn with_definition(env: &Environment, name: &str) -> Environment {
        let declaration = Declaration::Defn(DefinitionVal {
            base: ConstantVal {
                name: n(name),
                level_params: Vec::new(),
                type_: Expr::sort(Level::one()),
            },
            value: Expr::sort(Level::zero()),
            hints: ReducibilityHints::Abbrev,
            safety: DefinitionSafety::Safe,
            all: vec![n(name)],
        });
        let Outcome::Complete(admitted) =
            admit(env, declaration, Budget::for_stack_bytes(2 * 1024 * 1024))
        else {
            panic!("fixture admission did not complete");
        };
        let CouncilOutcome::Agreed(checked) = convene(&Council::nobody_was_asked(), admitted)
        else {
            panic!("fixture definition was not accepted");
        };
        let Outcome::Complete(Published::Committed(DeclarationCommitted::Published(result))) =
            checked.publish(
                DeclarationBudget::default(),
                CollisionBudget::default(),
                None,
            )
        else {
            panic!("checked fixture was not published");
        };
        result.environment
    }

    #[test]
    fn only_the_owned_suffix_is_exported_under_exact_limits() {
        let base = register(
            &with_definition(&Environment::new(), "Imported"),
            &n("Imported"),
        )
        .unwrap();
        let local = with_definition(&with_definition(&base, "Local.a"), "Local.b");
        let result = register(&register(&local, &n("Local.b")).unwrap(), &n("Local.a")).unwrap();
        let root = result.logical_root(&KVMap::new());
        let rows = registrations(&base, &result, usize::MAX).unwrap().unwrap();
        assert_eq!(rows.declarations, [n("Local.a"), n("Local.b")]);
        assert_eq!(rows.work, rows.bytes_examined + 3);
        assert_eq!(
            registrations(&base, &result, rows.work).unwrap(),
            Some(rows.clone())
        );
        assert_eq!(
            registrations(&base, &result, rows.work - 1),
            Err(MacroInlineError::Limit)
        );
        let untouched = registrations(&base, &base, 0).unwrap().unwrap();
        assert!(untouched.declarations.is_empty());
        assert_eq!(untouched.work, 0);
        assert_eq!(untouched.bytes_examined, 0);
        assert_eq!(result.logical_root(&KVMap::new()), root);
    }

    #[test]
    fn imported_tags_cannot_be_reassigned_to_the_exporting_module() {
        let base = with_definition(&Environment::new(), "Imported");
        let result = register(&base, &n("Imported")).unwrap();
        assert_eq!(registrations(&base, &result, usize::MAX).unwrap(), None);
    }

    #[test]
    fn malformed_duplicate_foreign_and_changed_prefixes_are_refused() {
        let env = with_definition(&with_definition(&Environment::new(), "a"), "b");
        let base = register(&env, &n("a")).unwrap();
        let rewritten = register(&env, &n("b")).unwrap();
        for result in [&env, &rewritten] {
            assert_eq!(
                registrations(&base, result, usize::MAX),
                Err(MacroInlineError::Malformed)
            );
        }
        let twice = register(&base, &n("a")).unwrap();
        assert_eq!(
            registrations(&Environment::new(), &twice, usize::MAX),
            Err(MacroInlineError::Duplicate(n("a")))
        );
        let mut missing = MAGIC.to_vec();
        write_name(&n("Missing"), &mut missing).unwrap();
        for payload in [Vec::new(), missing] {
            let malformed = env
                .register_extension(descriptor())
                .unwrap()
                .push_extension_entry(&journal_name(), payload)
                .unwrap();
            assert!(registrations(&Environment::new(), &malformed, usize::MAX).is_err());
        }
        let mut foreign = descriptor();
        foreign.provenance = PayloadProvenance::Opaque;
        let foreign = env.register_extension(foreign).unwrap();
        assert_eq!(
            registrations(&Environment::new(), &foreign, usize::MAX),
            Err(MacroInlineError::Malformed)
        );
    }
}
