//! Global extra overrides may target a dependency, but never an unrelated root.
//! Index only referenced names; metadata still requires an admitted declaration.
use super::*;

pub(super) struct Scopes<'a> {
    indices: BTreeMap<&'a Name, usize>,
    owners: BTreeMap<Name, Vec<(usize, &'a ConstantInfo)>>,
    work_left: u64,
}

impl<'a> Scopes<'a> {
    pub(super) fn new(
        checked: &'a CheckedOleanSet,
        rows: &[metadata::ReducibilityExtraEntry],
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
            result.owners.entry(row.declaration.clone()).or_default();
        }
        for (index, module) in checked.modules.iter().enumerate() {
            result.tick()?;
            result.indices.insert(&module.name, index);
            for constant in &module.decoded.constants {
                result.tick()?;
                if let Some(owners) = result.owners.get_mut(constant.name()) {
                    owners.try_reserve(1).map_err(|_| {
                        SourceOleanImportError::Limit("reducibility extra ownership allocation")
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
                "reducibility extra import-closure work",
            ))?;
        Ok(())
    }

    pub(super) fn validate(
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
            .ok_or_else(|| error("a reducibility override names no admitted declaration"))?;
        if origin.find(declaration) == Some(target) {
            return Ok(());
        }
        let mut pending = vec![module];
        let mut seen = HashSet::new();
        while let Some(index) = pending.pop() {
            self.tick()?;
            seen.try_reserve(1).map_err(|_| {
                SourceOleanImportError::Limit("reducibility extra import-closure allocation")
            })?;
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
                    SourceOleanImportError::Internal(
                        "reducibility extra import graph is incomplete",
                    ),
                )?;
                pending.try_reserve(1).map_err(|_| {
                    SourceOleanImportError::Limit("reducibility extra import-closure allocation")
                })?;
                pending.push(dependency);
            }
        }
        Err(error(
            "a reducibility override is outside this module's checked import closure",
        ))
    }
}

pub(super) fn error(
    module: &Name,
    declaration: &Name,
    error: fln_elab::reducibility::ReducibilityError,
) -> SourceOleanImportError {
    use fln_elab::reducibility::ReducibilityError;
    let reason = match error {
        ReducibilityError::Limit => {
            return SourceOleanImportError::Limit("reducibility journal");
        }
        ReducibilityError::UnknownDeclaration(_) => {
            "a reducibility status names no admitted declaration"
        }
        ReducibilityError::Malformed | ReducibilityError::Instances(_) => {
            "malformed reducibility status"
        }
    };
    SourceOleanImportError::Metadata {
        module: module.clone(),
        declaration: declaration.clone(),
        reason,
    }
}
