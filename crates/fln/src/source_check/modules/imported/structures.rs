//! Imported structure metadata uses the declaring module's actual checked
//! constructors/projections. Parent targets belong to that module's import world.
use super::*;
use fln_elab::records::RecordError;
use fln_elab::records::imported::{StructureEntry, StructureField, StructureParent};

/// Both values came from checked declarations, but decoding does not preserve
/// allocation identity. Charge the exact structural comparison before using it
/// as metadata ownership evidence.
fn same_interface(left: &ConstantInfo, right: &ConstantInfo, work_left: &mut u64) -> Result<bool> {
    let mut remaining = usize::try_from(*work_left)
        .map_err(|_| SourceOleanImportError::Limit("structure interface comparison work"))?;
    let result = fln_elab::records::imported::same_interface(left, right, &mut remaining);
    *work_left = remaining as u64;
    result.map_err(|problem| {
        if problem == RecordError::ResourceLimit {
            SourceOleanImportError::Limit("structure interface comparison work")
        } else {
            SourceOleanImportError::Internal("structure interface comparison")
        }
    })
}

fn validate_owner(
    owners: &mut AttributeOwners<'_>,
    active: &Environment,
    module: &Name,
    declaration: &Name,
    work_left: &mut u64,
) -> Result<()> {
    let error = |reason| SourceOleanImportError::Metadata {
        module: module.clone(),
        declaration: declaration.clone(),
        reason,
    };
    let position = owners
        .declarations
        .binary_search_by(|info| info.constant_val().name.cmp(declaration))
        .map_err(|_| {
            error("a structure interface does not belong to this module's checked declarations")
        })?;
    let admitted = active
        .find(declaration)
        .ok_or_else(|| error("a structure interface has no active admitted declaration"))?;
    if !same_interface(owners.declarations[position], admitted, work_left)? {
        return Err(error(
            "a structure interface differs from its active admitted declaration",
        ));
    }
    if !owners.seen.insert(declaration.clone()) {
        return Err(error("duplicate structure interface ownership row"));
    }
    Ok(())
}

pub(super) struct Scopes<'a> {
    indices: BTreeMap<&'a Name, usize>,
    owners: BTreeMap<Name, Vec<(usize, &'a ConstantInfo)>>,
    work_left: u64,
}

impl<'a> Scopes<'a> {
    pub(super) fn new(
        checked: &'a CheckedOleanSet,
        rows: &[metadata::StructureEntry],
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
            for parent in row
                .fields
                .iter()
                .filter_map(|field| field.subobject.as_ref())
                .chain(row.parents.iter().map(|parent| &parent.name))
            {
                result.tick()?;
                result.owners.entry(parent.clone()).or_default();
            }
        }
        for (index, module) in checked.modules.iter().enumerate() {
            result.tick()?;
            result.indices.insert(&module.name, index);
            for constant in &module.decoded.constants {
                result.tick()?;
                if let Some(owners) = result.owners.get_mut(constant.name()) {
                    owners.try_reserve(1).map_err(|_| {
                        SourceOleanImportError::Limit("structure parent ownership allocation")
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
                "structure parent import-closure work",
            ))?;
        Ok(())
    }

    fn validate(
        &mut self,
        checked: &CheckedOleanSet,
        origin: &Environment,
        active: &Environment,
        module: usize,
        record: &Name,
        parent: &Name,
    ) -> Result<()> {
        self.tick()?;
        let error = |reason| SourceOleanImportError::Metadata {
            module: checked.modules[module].name.clone(),
            declaration: record.clone(),
            reason,
        };
        let target = active
            .find(parent)
            .ok_or_else(|| error("a structure parent is not admitted"))?;
        if let Some(original) = origin.find(parent)
            && same_interface(original, target, &mut self.work_left)?
        {
            return Ok(());
        }
        let mut pending = vec![module];
        let mut seen = HashSet::new();
        while let Some(index) = pending.pop() {
            self.tick()?;
            seen.try_reserve(1).map_err(|_| {
                SourceOleanImportError::Limit("structure parent import-closure allocation")
            })?;
            if !seen.insert(index) {
                continue;
            }
            if let Some(owners) = self.owners.get(parent) {
                for (owner, constant) in owners {
                    self.work_left =
                        self.work_left
                            .checked_sub(1)
                            .ok_or(SourceOleanImportError::Limit(
                                "structure parent owner comparison",
                            ))?;
                    if *owner == index && same_interface(constant, target, &mut self.work_left)? {
                        return Ok(());
                    }
                }
            }
            for import in &checked.modules[index].decoded.module.imports {
                self.tick()?;
                let dependency = self.indices.get(&import.module).copied().ok_or(
                    SourceOleanImportError::Internal("structure parent import graph is incomplete"),
                )?;
                pending.try_reserve(1).map_err(|_| {
                    SourceOleanImportError::Limit("structure parent import-closure allocation")
                })?;
                pending.push(dependency);
            }
        }
        Err(error(
            "a structure parent is outside this module's checked import closure",
        ))
    }
}

#[allow(clippy::too_many_arguments)]
pub(super) fn module(
    checked: &CheckedOleanSet,
    origin: &Environment,
    active: &Environment,
    index: usize,
    count: usize,
    rows: &mut impl Iterator<Item = metadata::StructureEntry>,
    scopes: &mut Scopes<'_>,
    limits: &SourceOleanImportLimits,
    cancellation: Option<&dyn CancellationProbe>,
) -> Result<Outcome<Vec<StructureEntry>>> {
    let module = &checked.modules[index].name;
    let mut pending = Vec::new();
    pending
        .try_reserve_exact(count)
        .map_err(|_| SourceOleanImportError::Limit("structure metadata allocation"))?;
    let mut ownership = BTreeSet::new();
    let mut previous: Option<Name> = None;
    for _ in 0..count {
        if cancellation.is_some_and(CancellationProbe::is_cancelled) {
            return Ok(Outcome::Inconclusive(Inconclusive::cancelled(
                "source-olean/structure",
            )));
        }
        let row = rows.next().ok_or(SourceOleanImportError::Internal(
            "structure count changed during decode",
        ))?;
        if previous
            .as_ref()
            .is_some_and(|previous| !previous.quick_lt(&row.name))
        {
            return Err(SourceOleanImportError::Metadata {
                module: module.clone(),
                declaration: row.name,
                reason: "this module's structure metadata is not strictly sorted",
            });
        }
        previous = Some(row.name.clone());
        ownership.insert(row.name.clone());
        // Bind the complete physical interface to declarations in this same
        // module, including constructors and private generated projections.
        if let Some(ConstantInfo::Induct(family)) = active.find(&row.name) {
            for constructor in &family.ctors {
                ownership.insert(constructor.clone());
            }
        }
        for projection in row
            .fields
            .iter()
            .map(|field| &field.projection)
            .chain(row.parents.iter().map(|parent| &parent.projection))
        {
            ownership.insert(projection.clone());
        }
        if ownership.len() > limits.metadata.max_entries {
            return Err(SourceOleanImportError::Limit(
                "structure interface ownership rows",
            ));
        }
        let mut parents = BTreeSet::new();
        for parent in row
            .fields
            .iter()
            .filter_map(|field| field.subobject.as_ref())
            .chain(row.parents.iter().map(|parent| &parent.name))
        {
            if cancellation.is_some_and(CancellationProbe::is_cancelled) {
                return Ok(Outcome::Inconclusive(Inconclusive::cancelled(
                    "source-olean/structure-parent",
                )));
            }
            if parents.insert(parent.clone()) {
                scopes.validate(checked, origin, active, index, &row.name, parent)?;
            }
        }
        pending.push(StructureEntry {
            name: row.name,
            fields: row
                .fields
                .into_iter()
                .map(|field| StructureField {
                    name: field.name,
                    projection: field.projection,
                    subobject: field.subobject,
                    binder_info: field.binder_info,
                })
                .collect(),
            parents: row
                .parents
                .into_iter()
                .map(|parent| StructureParent {
                    name: parent.name,
                    subobject: parent.subobject,
                    projection: parent.projection,
                })
                .collect(),
        });
    }
    let mut owners = AttributeOwners::new(
        &checked.modules[index].decoded.constants,
        ownership.len(),
        limits.check.max_declarations,
        limits.metadata.max_entries,
    )?;
    for declaration in ownership {
        if cancellation.is_some_and(CancellationProbe::is_cancelled) {
            return Ok(Outcome::Inconclusive(Inconclusive::cancelled(
                "source-olean/structure-owner",
            )));
        }
        validate_owner(
            &mut owners,
            active,
            module,
            &declaration,
            &mut scopes.work_left,
        )?;
    }
    Ok(Outcome::Complete(pending))
}

pub(super) fn error(module: &Name, record: &Name, error: RecordError) -> SourceOleanImportError {
    if error == RecordError::ResourceLimit {
        return SourceOleanImportError::Limit("imported structure journal");
    }
    SourceOleanImportError::Metadata {
        module: module.clone(),
        declaration: record.clone(),
        reason: "structure metadata disagrees with its admitted constructor, projections or parents",
    }
}

#[cfg(test)]
#[path = "structures/tests.rs"]
mod tests;
