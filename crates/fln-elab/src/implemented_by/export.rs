//! Final module-owned executable attributes. Imported prefixes are retained
//! exactly and never exported under a downstream module's identity.
use super::*;
use std::collections::BTreeSet;
use std::sync::Arc;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Registrations {
    pub entries: Vec<(Name, Name)>,
    pub work: usize,
    pub bytes_examined: usize,
}

pub fn registrations(
    base: &Environment,
    result: &Environment,
    max_work: usize,
) -> Result<Option<Registrations>, ImplementedByError> {
    let mut remaining = max_work;
    let mut charge = |amount: usize| {
        remaining = remaining
            .checked_sub(amount)
            .ok_or(ImplementedByError::Limit)?;
        Ok::<_, ImplementedByError>(())
    };
    // Validate all rows, including overwritten values, signatures and chains.
    let table =
        ImplementedByTable::read_metered(result, &mut charge).map_err(|error| match error {
            ImplementedByReadError::Registry(error) | ImplementedByReadError::Budget(error) => {
                error
            }
        })?;
    let prior = base.extension(&journal_name());
    let Some(current) = result.extension(&journal_name()) else {
        return if prior.is_some() {
            Err(ImplementedByError::Malformed)
        } else {
            Ok(Some(Registrations {
                entries: Vec::new(),
                work: max_work - remaining,
                bytes_examined: 0,
            }))
        };
    };
    let mut bytes_examined = 0usize;
    charge(current.len())?;
    for entry in current.entries() {
        // The table's metered read already charged payload decoding.
        bytes_examined = bytes_examined
            .checked_add(entry.payload.len())
            .ok_or(ImplementedByError::Limit)?;
    }
    charge(current.len())?;
    let mut entries = current.entries();
    if let Some(prior) = prior {
        if prior.descriptor != current.descriptor || prior.len() > current.len() {
            return Err(ImplementedByError::Malformed);
        }
        for old in prior.entries() {
            charge(1)?;
            let new = entries.next().ok_or(ImplementedByError::Malformed)?;
            if Arc::ptr_eq(&old.payload, &new.payload) {
                continue;
            }
            for payload in [&old.payload, &new.payload] {
                charge(payload.len())?;
                bytes_examined = bytes_examined
                    .checked_add(payload.len())
                    .ok_or(ImplementedByError::Limit)?;
            }
            if old != new {
                return Err(ImplementedByError::Malformed);
            }
        }
    }
    let mut owned = BTreeSet::new();
    for entry in entries {
        charge(1)?;
        charge(entry.payload.len())?;
        bytes_examined = bytes_examined
            .checked_add(entry.payload.len())
            .ok_or(ImplementedByError::Limit)?;
        let (declaration, _) = decode_entry(&entry.payload)?;
        if base.contains(&declaration) {
            return Ok(None);
        }
        owned.insert(declaration);
    }
    let mut final_entries = Vec::new();
    for declaration in owned {
        charge(1)?;
        let value = table
            .get(&declaration)
            .ok_or(ImplementedByError::Malformed)?;
        final_entries.push((declaration, value.clone()));
    }
    Ok(Some(Registrations {
        entries: final_entries,
        work: max_work - remaining,
        bytes_examined,
    }))
}
