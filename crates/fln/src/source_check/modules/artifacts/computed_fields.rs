//! Export the pin's computed-field attributes only with the complete checked
//! representation. Imported membership tags never recreate runtime provenance.
use super::*;
use fln_elab::computed_fields::{self as fields, ComputedFieldEntry};
use fln_olean::source_extensions::{InlineEntry, InlineKind, ReducibilityStatus};

fn invalid(module: &Name, reason: &'static str) -> SourceModuleCheckError {
    SourceModuleCheckError::Extension {
        module: module.clone(),
        extension: fields::journal_name(),
        reason,
    }
}

pub(super) fn capture(
    module: &Name,
    base: &Environment,
    checked: &Environment,
    meter: &mut Meter,
) -> Result<Vec<ComputedFieldEntry>, SourceModuleCheckError> {
    let Some(journal) = checked.extension(&fields::journal_name()) else {
        return Ok(Vec::new());
    };
    let inherited = base.extension(&fields::journal_name());
    let mut unchanged = inherited.is_some_and(|previous| previous.len() == journal.len());
    let mut prior = inherited
        .into_iter()
        .flat_map(|previous| previous.entries());
    for entry in journal.entries() {
        meter.work(1)?;
        meter.bytes(entry.payload.len())?;
        unchanged &= prior.next() == Some(entry);
    }
    if unchanged {
        return Ok(Vec::new());
    }
    let remaining = meter.limits.max_work.saturating_sub(meter.work);
    let allowance = (remaining / 2).min(100_000);
    meter.work(allowance)?;
    let families: BTreeSet<_> = fields::families(
        checked,
        fln_elab::records::RecordBudget {
            max_binders: allowance,
            max_nodes: allowance,
        },
    )
    .map_err(|error| match error {
        fields::ComputedFieldError::ResourceLimit => SourceModuleCheckError::Limit {
            resource: "module work",
            limit: meter.limits.max_work,
        },
        _ => invalid(module, "invalid computed-field generation provenance"),
    })?
    .into_iter()
    .collect();
    let mut owned = BTreeMap::new();
    for stored in journal.entries() {
        meter.work(stored.payload.len().saturating_add(1))?;
        let entry = fields::decode_entry(&stored.payload)
            .map_err(|_| invalid(module, "invalid computed-field generation provenance"))?;
        if !families.contains(&entry.family) {
            continue;
        }
        let implementation = Name::str(entry.family.clone(), "_impl");
        match (base.contains(&entry.family), base.contains(&implementation)) {
            (true, true) => continue,
            (false, false) => {}
            _ => {
                return Err(invalid(
                    module,
                    "a computed-field module must own its complete implementation family",
                ));
            }
        }
        owned.insert(entry.family.clone(), entry);
    }
    Ok(owned.into_values().collect())
}

/// Source generation already checked every candidate. This final export gate
/// ensures the chosen artifact view retains every corresponding compiler cache
/// and executable edge before the writer can publish any bytes.
pub(super) fn finish(
    module: &Name,
    entries: &[ComputedFieldEntry],
    checked: &Environment,
    layouts: &BTreeSet<Name>,
    metadata: &mut SourceMetadata,
    meter: &mut Meter,
) -> Result<(), SourceModuleCheckError> {
    let edges: BTreeMap<_, _> = metadata
        .implemented_by
        .iter()
        .map(|entry| (entry.declaration.clone(), entry.implementation.clone()))
        .collect();
    for entry in entries {
        meter.work(entry.fields.len().saturating_add(1))?;
        let implementation = Name::str(entry.family.clone(), "_impl");
        if !layouts.contains(&entry.family) || !layouts.contains(&implementation) {
            return Err(invalid(
                module,
                "computed-field artifacts require supported logical and implementation compiler layouts",
            ));
        }
        let Some(ConstantInfo::Induct(family)) = checked.find(&entry.family) else {
            return Err(invalid(module, "missing checked computed-field family"));
        };
        let cases_on = Name::str(entry.family.clone(), "casesOn");
        let implementation_cases = Name::str(implementation, "casesOn");
        if !metadata.aux_recursors.contains(&implementation_cases)
            || !metadata.reducibility.iter().any(|status| {
                status.declaration == implementation_cases
                    && status.status == ReducibilityStatus::Reducible
            })
        {
            return Err(invalid(
                module,
                "computed-field artifacts require their checked auxiliary eliminator metadata",
            ));
        }
        let mut originals = vec![cases_on.clone()];
        originals.extend(family.ctors.iter().cloned());
        originals.extend(entry.fields.iter().cloned());
        for original in originals {
            meter.work(1)?;
            if edges.get(&original) != Some(&Name::str(original.clone(), "_override")) {
                return Err(invalid(
                    module,
                    "computed-field artifacts require every checked executable replacement",
                ));
            }
        }
        for field in &entry.fields {
            meter.work(1)?;
            if !metadata.computed_fields.contains(field) || !metadata.noncomputable.contains(field)
            {
                return Err(invalid(
                    module,
                    "computed-field artifacts require their logical getter attributes",
                ));
            }
        }
        let mut inline = BTreeSet::from([Name::str(cases_on, "_override")]);
        for constructor in &family.ctors {
            meter.work(1)?;
            let Some(ConstantInfo::Ctor(info)) = checked.find(constructor) else {
                return Err(invalid(
                    module,
                    "missing checked computed-field constructor",
                ));
            };
            if info.num_fields == 0 {
                inline.insert(Name::str(constructor.clone(), "_override"));
            }
        }
        for field in &entry.inline_fields {
            meter.work(1)?;
            inline.insert(field.clone());
            inline.insert(Name::str(field.clone(), "_override"));
        }
        for declaration in inline {
            meter.work(1)?;
            if let Some(previous) = metadata
                .inline
                .iter()
                .find(|row| row.declaration == declaration)
            {
                if previous.kind != InlineKind::Inline {
                    return Err(invalid(
                        module,
                        "conflicting computed-field inlining attributes",
                    ));
                }
            } else {
                metadata.inline.push(InlineEntry {
                    declaration,
                    kind: InlineKind::Inline,
                });
            }
        }
    }
    Ok(())
}
