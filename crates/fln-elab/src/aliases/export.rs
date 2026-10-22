//! A checked module exports only the chronological suffix of its alias journal.
//! Targets may belong to imports: re-exporting them is the purpose of `export`.
use super::*;
use std::sync::Arc;

pub fn journal_name() -> Name {
    extension_name()
}

pub fn supports(candidate: &ExtensionDescriptor) -> bool {
    *candidate == descriptor()
}

#[derive(Debug, Default, PartialEq, Eq)]
pub struct Registrations {
    pub entries: Vec<(Name, Name)>,
    pub work: usize,
    pub bytes_examined: usize,
}

struct Meter {
    remaining: usize,
    bytes: usize,
}

impl Meter {
    fn charge(&mut self, amount: usize) -> Result<(), AliasError> {
        self.remaining = self
            .remaining
            .checked_sub(amount)
            .ok_or(AliasError::Limit)?;
        Ok(())
    }

    fn payload(&mut self, bytes: &[u8]) -> Result<(), AliasError> {
        if bytes.len() > MAX_ENTRY_BYTES {
            return Err(AliasError::Limit);
        }
        self.charge(bytes.len())?;
        self.bytes = self
            .bytes
            .checked_add(bytes.len())
            .ok_or(AliasError::Limit)?;
        Ok(())
    }
}

/// Preserve the exact appended history, not the alias-sorted resolution table.
/// Descriptor/prefix checks forbid replacing imported metadata. All names still
/// refer to existing declarations; this function cannot admit a declaration.
pub fn registrations(
    base: &Environment,
    result: &Environment,
    max_work: usize,
) -> Result<Registrations, AliasError> {
    let prior = base.extension(&extension_name());
    let Some(current) = result.extension(&extension_name()) else {
        return if prior.is_some() {
            Err(AliasError::Malformed)
        } else {
            Ok(Registrations::default())
        };
    };
    if current.descriptor != descriptor()
        || prior
            .is_some_and(|old| old.descriptor != current.descriptor || old.len() > current.len())
    {
        return Err(AliasError::Malformed);
    }
    if current.len() > MAX_ROWS {
        return Err(AliasError::Limit);
    }
    let inherited_count = prior.map_or(0, |old| old.len());
    let mut inherited = prior.map(|old| old.entries());
    let mut meter = Meter {
        remaining: max_work,
        bytes: 0,
    };
    let mut entries = Vec::new();
    for (index, row) in current.entries().enumerate() {
        meter.charge(1)?;
        if index < inherited_count {
            let old = inherited
                .as_mut()
                .and_then(Iterator::next)
                .ok_or(AliasError::Malformed)?;
            if !Arc::ptr_eq(&old.payload, &row.payload) {
                meter.payload(&old.payload)?;
                meter.payload(&row.payload)?;
                if old != row {
                    return Err(AliasError::Malformed);
                }
            }
        }
        // Decode even inherited entries: malformed data cannot become valid
        // merely by appearing in both caller-supplied environment snapshots.
        meter.payload(&row.payload)?;
        let Some(mut bytes) = row.payload.strip_prefix(MAGIC) else {
            return Err(AliasError::Malformed);
        };
        let alias = read_name(&mut bytes).map_err(codec)?;
        let declaration = read_name(&mut bytes).map_err(codec)?;
        if !bytes.is_empty() || alias.is_anonymous() || declaration.is_anonymous() {
            return Err(AliasError::Malformed);
        }
        if !result.contains(&declaration) {
            return Err(AliasError::UnknownDeclaration(declaration));
        }
        if index >= inherited_count {
            entries.push((alias, declaration));
        }
    }
    Ok(Registrations {
        entries,
        work: max_work - meter.remaining,
        bytes_examined: meter.bytes,
    })
}

#[cfg(test)]
mod tests;
