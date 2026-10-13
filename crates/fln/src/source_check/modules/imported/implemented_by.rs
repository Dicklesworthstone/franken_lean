//! Replacement targets belong to the owner's import world, not the union of
//! all roots checked in this import call. Index only referenced target names.
use super::*;
use fln_elab::implemented_by::{ImplementedByError, ImplementedByTable};

pub(super) struct Scopes<'a> {
    indices: BTreeMap<&'a Name, usize>,
    owners: BTreeMap<Name, Vec<(usize, &'a ConstantInfo)>>,
    work_left: u64,
}

impl<'a> Scopes<'a> {
    pub(super) fn new(
        checked: &'a CheckedOleanSet,
        rows: &[metadata::ImplementedByEntry],
        work_left: u64,
    ) -> Result<Self> {
        let mut result = Self {
            indices: BTreeMap::new(),
            owners: BTreeMap::new(),
            work_left,
        };
        if rows.is_empty() {
            return Ok(result);
        }
        for row in rows {
            result.tick()?;
            result.owners.entry(row.implementation.clone()).or_default();
        }
        for (index, module) in checked.modules.iter().enumerate() {
            result.tick()?;
            result.indices.insert(&module.name, index);
            for constant in &module.decoded.constants {
                result.tick()?;
                if let Some(owners) = result.owners.get_mut(constant.name()) {
                    owners.try_reserve(1).map_err(|_| {
                        SourceOleanImportError::Limit("implemented_by target ownership allocation")
                    })?;
                    owners.push((index, constant));
                }
            }
        }
        Ok(result)
    }

    fn tick(&mut self) -> Result<()> {
        self.work_left = self
            .work_left
            .checked_sub(1)
            .ok_or(SourceOleanImportError::Limit(
                "implemented_by target import-closure work",
            ))?;
        Ok(())
    }

    pub(super) fn validate(
        &mut self,
        checked: &CheckedOleanSet,
        origin: &Environment,
        active: &Environment,
        module: usize,
        row: &metadata::ImplementedByEntry,
    ) -> Result<()> {
        self.tick()?;
        let error = |reason| SourceOleanImportError::Metadata {
            module: checked.modules[module].name.clone(),
            declaration: row.declaration.clone(),
            reason,
        };
        let target = active
            .find(&row.implementation)
            .ok_or_else(|| error("implemented_by target is not an admitted declaration"))?;
        if origin.find(&row.implementation) == Some(target) {
            return Ok(());
        }
        let mut pending = vec![module];
        let mut seen = HashSet::new();
        while let Some(index) = pending.pop() {
            self.tick()?;
            seen.try_reserve(1).map_err(|_| {
                SourceOleanImportError::Limit("implemented_by target import-closure allocation")
            })?;
            if !seen.insert(index) {
                continue;
            }
            if self.owners.get(&row.implementation).is_some_and(|owners| {
                owners
                    .iter()
                    .any(|(owner, constant)| *owner == index && *constant == target)
            }) {
                return Ok(());
            }
            for import in &checked.modules[index].decoded.module.imports {
                self.tick()?;
                let dependency = self.indices.get(&import.module).copied().ok_or(
                    SourceOleanImportError::Internal(
                        "implemented_by target import graph is incomplete",
                    ),
                )?;
                pending.try_reserve(1).map_err(|_| {
                    SourceOleanImportError::Limit("implemented_by target import-closure allocation")
                })?;
                pending.push(dependency);
            }
        }
        Err(error(
            "implemented_by target is outside this module's checked import closure",
        ))
    }
}

pub(super) fn error(
    module: &Name,
    declaration: &Name,
    error: ImplementedByError,
) -> SourceOleanImportError {
    let reason = match error {
        ImplementedByError::Limit => {
            return SourceOleanImportError::Limit("implemented_by attribute journal");
        }
        ImplementedByError::UnknownDeclaration(_) => "implemented_by names no admitted declaration",
        ImplementedByError::InvalidSignature { .. } => {
            "implemented_by target has a different type or universe arity"
        }
        ImplementedByError::SelfImplementation(_) => "implemented_by declaration implements itself",
        ImplementedByError::Cycle(_) => "implemented_by replacement cycle",
        ImplementedByError::Malformed => "malformed implemented_by attribute journal",
    };
    SourceOleanImportError::Metadata {
        module: module.clone(),
        declaration: declaration.clone(),
        reason,
    }
}

pub(super) fn validate_journal(env: &Environment) -> Result<()> {
    ImplementedByTable::read(env)
        .map(|_| ())
        .map_err(|problem| {
            let declaration = match &problem {
                ImplementedByError::UnknownDeclaration(name)
                | ImplementedByError::SelfImplementation(name)
                | ImplementedByError::Cycle(name) => name.clone(),
                ImplementedByError::InvalidSignature { declaration, .. } => declaration.clone(),
                _ => fln_elab::implemented_by::journal_name(),
            };
            error(
                &fln_elab::implemented_by::journal_name(),
                &declaration,
                problem,
            )
        })
}
