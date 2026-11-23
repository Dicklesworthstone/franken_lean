//! A module may register dependency lemmas, but never names from sibling roots.
//! Stored paths are retained, with every named key checked in the same closure.
use super::*;

pub(super) struct Scopes<'a> {
    indices: BTreeMap<&'a Name, usize>,
    owners: BTreeMap<Name, Vec<(usize, &'a ConstantInfo)>>,
    work_left: u64,
}

fn names(row: &metadata::SymmEntry) -> impl Iterator<Item = &Name> {
    std::iter::once(&row.declaration).chain(row.keys.iter().filter_map(|key| match key {
        metadata::DiscrTreeKey::Const(name, _) | metadata::DiscrTreeKey::Proj(name, _, _) => {
            Some(name)
        }
        _ => None,
    }))
}

impl<'a> Scopes<'a> {
    pub(super) fn new(
        checked: &'a CheckedOleanSet,
        rows: &[metadata::SymmEntry],
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
            for name in names(row) {
                result.tick()?;
                result.owners.entry(name.clone()).or_default();
            }
        }
        for (index, module) in checked.modules.iter().enumerate() {
            result.tick()?;
            result.indices.insert(&module.name, index);
            for constant in &module.decoded.constants {
                result.tick()?;
                if let Some(owners) = result.owners.get_mut(constant.name()) {
                    owners.try_reserve(1).map_err(|_| {
                        SourceOleanImportError::Limit("symmetry ownership allocation")
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
                "symmetry import-closure work",
            ))?;
        Ok(())
    }

    pub(super) fn validate_row(
        &mut self,
        checked: &CheckedOleanSet,
        origin: &Environment,
        active: &Environment,
        module: usize,
        row: &metadata::SymmEntry,
    ) -> Result<()> {
        for declaration in names(row) {
            self.validate(checked, origin, active, module, declaration)?;
        }
        Ok(())
    }

    fn validate(
        &mut self,
        checked: &CheckedOleanSet,
        origin: &Environment,
        active: &Environment,
        module: usize,
        declaration: &Name,
    ) -> Result<()> {
        self.tick()?;
        let error = |reason| SourceOleanImportError::Metadata {
            module: checked.modules[module].name.clone(),
            declaration: declaration.clone(),
            reason,
        };
        let target = active
            .find(declaration)
            .ok_or_else(|| error("a symmetry entry names no admitted declaration"))?;
        if origin.find(declaration) == Some(target) {
            return Ok(());
        }
        let mut pending = vec![module];
        let mut seen = HashSet::new();
        while let Some(index) = pending.pop() {
            self.tick()?;
            seen.try_reserve(1)
                .map_err(|_| SourceOleanImportError::Limit("symmetry import-closure allocation"))?;
            if !seen.insert(index) {
                continue;
            }
            if self.owners.get(declaration).is_some_and(|owners| {
                owners
                    .iter()
                    .any(|(owner, constant)| *owner == index && *constant == target)
            }) {
                return Ok(());
            }
            for import in &checked.modules[index].decoded.module.imports {
                self.tick()?;
                let dependency = self.indices.get(&import.module).copied().ok_or(
                    SourceOleanImportError::Internal("symmetry import graph is incomplete"),
                )?;
                pending.try_reserve(1).map_err(|_| {
                    SourceOleanImportError::Limit("symmetry import-closure allocation")
                })?;
                pending.push(dependency);
            }
        }
        Err(error(
            "a symmetry entry is outside this module's checked import closure",
        ))
    }
}

pub(super) fn error(
    module: &Name,
    error: fln_elab::symm::SymmRegistryError,
) -> SourceOleanImportError {
    SourceOleanImportError::Symm {
        module: module.clone(),
        error,
    }
}
