//! Export the pin's computed-field attributes only with the complete checked
//! representation. Imported membership tags alone never recreate runtime provenance.
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
