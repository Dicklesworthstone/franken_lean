//! Inert field tags and optional recovery of a completely checked native model.
use super::*;
use fln_elab::computed_fields::ComputedFieldError;
use fln_elab::records::RecordBudget;

/// Count candidates per owning module before reserving validation work. The
/// same parent can carry foreign tags in separate modules, so a closure-wide
/// set of parent names would undercount the actual recovery attempts.
pub(super) fn candidate_count(
    reports: &[SourceMetadataReport],
    fields: &[Name],
    work_left: &mut usize,
) -> Result<usize> {
    let mut fields = fields;
    let mut count = 0_usize;
    for report in reports {
        if report.computed_fields == 0 {
            continue;
        }
        *work_left = work_left
            .checked_sub(report.computed_fields.saturating_add(1))
            .ok_or(SourceOleanImportError::Limit(
                "computed-field metadata work",
            ))?;
        let (owned, rest) = fields.split_at_checked(report.computed_fields).ok_or(
            SourceOleanImportError::Internal("computed-field count changed before recovery"),
        )?;
        let mut parents = HashSet::new();
        parents.try_reserve(owned.len()).map_err(|_| {
            SourceOleanImportError::Limit("computed-field recovery ownership allocation")
        })?;
        parents.extend(owned.iter().map(Name::parent));
        count = count
            .checked_add(parents.len())
            .ok_or(SourceOleanImportError::Limit(
                "computed-field recovery candidate count",
            ))?;
        fields = rest;
    }
    if !fields.is_empty() {
        return Err(SourceOleanImportError::Internal(
            "computed-field tags escaped their module inventory",
        ));
    }
    Ok(count)
}

fn reserve(left: &mut usize, phases: usize, remaining_families: usize) -> Result<RecordBudget> {
    let mut budget = RecordBudget::default();
    // Reserve a fair share for every remaining candidate. Spending a complete
    // maximum allowance on each early (often inert) tag would otherwise impose
    // a fixed family-count ceiling even when all declarations are tiny.
    let divisor = phases
        .checked_mul(remaining_families)
        .filter(|divisor| *divisor != 0)
        .ok_or(SourceOleanImportError::Limit(
            "computed-field metadata work",
        ))?;
    budget.max_nodes = budget.max_nodes.min(*left / divisor);
    if budget.max_nodes == 0 {
        return Err(SourceOleanImportError::Limit(
            "computed-field metadata work",
        ));
    }
    *left -= budget.max_nodes * phases;
    Ok(budget)
}

fn outcome<T>(
    module: &Name,
    result: std::result::Result<T, ComputedFieldError>,
) -> Result<Outcome<T>> {
    use fln_elab::constraint::unify::UnificationError;
    let error = match result {
        Ok(value) => return Ok(Outcome::Complete(value)),
        Err(error) => error,
    };
    if let ComputedFieldError::Reduction(error) = &error {
        let checked = match error.as_ref() {
            UnificationError::AssignmentCheck { outcome, .. }
            | UnificationError::ConversionCheck { outcome }
            | UnificationError::ConstraintCheck { outcome, .. } => Some(outcome.as_ref()),
            _ => None,
        };
        match checked {
            Some(Outcome::Inconclusive(reason)) => {
                return Ok(Outcome::Inconclusive(reason.clone()));
            }
            Some(Outcome::InternalFault(fault)) => {
                return Ok(Outcome::InternalFault(fault.clone()));
            }
            _ => {}
        }
    }
    Err(SourceOleanImportError::ComputedFields {
        module: module.clone(),
        error,
    })
}

/// Once a family matches the native generator, its generated inline policy
/// must also survive serialization. Foreign tags never enter this check.
fn validate_inline(
    env: &Environment,
    module: &Name,
    family: &Name,
    fields: &[Name],
    inline: &BTreeMap<Name, metadata::InlineKind>,
) -> Result<()> {
    let require = |name: Name, expected: bool| {
        if inline.get(&name).copied() == expected.then_some(metadata::InlineKind::Inline) {
            Ok(())
        } else {
            Err(SourceOleanImportError::Metadata {
                module: module.clone(),
                declaration: name,
                reason: "native computed-field inline metadata differs from generated policy",
            })
        }
    };
    require(
        Name::str(Name::str(family.clone(), "casesOn"), "_override"),
        true,
    )?;
    let Some(ConstantInfo::Induct(inductive)) = env.find(family) else {
        return Err(SourceOleanImportError::Internal(
            "a recovered computed family lost its checked inductive",
        ));
    };
    for constructor in &inductive.ctors {
        let Some(ConstantInfo::Ctor(info)) = env.find(constructor) else {
            return Err(SourceOleanImportError::Internal(
                "a recovered computed family lost a checked constructor",
            ));
        };
        if info.num_fields == 0 {
            require(Name::str(constructor.clone(), "_override"), true)?;
        }
    }
    for field in fields {
        let is_inline = inline.get(field) == Some(&metadata::InlineKind::Inline);
        if is_inline {
            require(Name::str(field.clone(), "_override"), true)?;
        }
    }
    Ok(())
}

pub(super) fn activate<R: Registrar>(
    activation: R,
    module: &Name,
    fields: &[Name],
    inline: &BTreeMap<Name, metadata::InlineKind>,
    kernel: fln_kernel::verdict::Budget,
    work_left: &mut usize,
    families_left: &mut usize,
) -> Result<Outcome<R>> {
    // The ordinary importer has already retained each checked tag once using
    // the pin's attribute contract. This pass only attempts native recovery.
    let mut activation = activation;
    let mut families: BTreeMap<Name, Vec<Name>> = BTreeMap::new();
    for field in fields {
        families
            .entry(field.parent())
            .or_default()
            .push(field.clone());
    }
    for (family, fields) in families {
        let inline_fields: Vec<_> = fields
            .iter()
            .filter(|field| inline.get(*field) == Some(&metadata::InlineKind::Inline))
            .cloned()
            .collect();
        let budget = reserve(
            work_left,
            fln_elab::computed_fields::RECOVERY_PHASES,
            *families_left,
        )?;
        *families_left = families_left
            .checked_sub(1)
            .ok_or(SourceOleanImportError::Internal(
                "computed-field recovery candidate count changed",
            ))?;
        let (next, recovered) = match outcome(
            module,
            activation.recover_computed_family(&family, &fields, &inline_fields, kernel, budget),
        )? {
            Outcome::Complete(next) => next,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        activation = next;
        if recovered {
            validate_inline(activation.environment(), module, &family, &fields, inline)?;
        }
    }
    Ok(Outcome::Complete(activation))
}
